# Vineflower 的 Rust 移植

行为基准是 Vineflower 1.12.0，提交 `b8273988af850e8cfb234ca08d129058502b032f`。比较一次反编译时，输入包括整组 class 文件、库的查找顺序、选项、启用的插件和运行原版的 JDK。同一段字节码可以对应多种合法源码，因此识别优先级、遍历顺序、编号和格式也属于兼容目标。上游 [ARCHITECTURE.md](../vineflower/ARCHITECTURE.md) 介绍算法背景，具体调用顺序以同版本源码为准。

## 使用原生入口

在仓库根目录运行以下命令，可以将一个归档反编译到输出目录。单个 class、目录和多个输入也走同一条处理路径。

```sh
cargo run --release --locked -- --folder input.jar output
```

库调用从 `Decompiler::new(Options)` 开始。`add_source` 登记需要写出的输入，`add_library` 登记用于类型查找的依赖。`decompile` 返回各根类的源码和行映射，`save` 按输出模式保存源码、目录和资源。每个输入单元先准备全部根类，再恢复各根类自己的导入表、计数器和源码映射器，依次写出。类关系和已发布的方法包装器在两阶段间共享。当前调度以单工作线程执行。`--legacy-saving` 是原版保留输入归档布局的保存模式。[库入口](src/engine/driver/mod.rs) · [命令行](src/bin/vineflower-rs.rs) · [保存器](src/engine/driver/saver.rs)

启用 `rename-members` 时，先建立类与接口的继承关系，再沿继承链传播可重命名方法的映射。接口方法、外部库和 native 方法会约束派生类的名称。随后用同一映射重新载入常量池与类路径，内部类的简单名沿用同一个命名器。[标识符转换](src/renamer/identifier_converter.rs)

IDEA 的 `@NotNull` 恢复位于 Java 方法主循环末段。启用插件及其 `resugar-idea-notnull` 选项后，根据不可见注解和语句图识别参数与返回值的插桩，删除后从本轮的清边步骤重新开始。命令行默认安装该插件，库调用可通过 `Options::idea_notnull` 控制。[IDEA 插件](src/decompiler/idea_not_null.rs)

## 从输入到编译单元

| 阶段 | 输入与产生的结果 | 上游入口 |
| --- | --- | --- |
| 类路径与命名 | 对自有输入和外部库建立索引，按需读取库元数据。启用符号重命名时，先更新符号映射，再建立根类、成员类、局部类与匿名类的关系 | `Fernflower.decompileContext`、`StructContext`、`ClassesProcessor.loadClasses` |
| 根类准备 | 开始根类的 import 和源码映射作用域，识别 lambda，初始化该编译单元内各类的 wrapper。没有 Code 的方法只需要处理参数等元数据 | `ClassesProcessor.processClass`、`ClassWrapper.init` |
| 通用方法 CFG | 解码 Code 和异常表，切分基本块并连边。从 max_locals 初始化变量计数器，依次清理不可达块、按条件展开 JSR、连接虚拟出口、清理 goto | `StructMethod.expandData`、`ControlFlowGraph`、`MethodProcessor.codeToJava` |
| 语言分派 | 在共同清理后，LanguageSpec 可以选择自己的 CFG passes、图解析器和后续 passes。默认 Java 路径在 CFG 构造与语句解析前分别留有插件调用点 | `MethodProcessor.codeToJava`、`LanguageSpec` |
| Java 保护区整理 | 处理循环保护区、恢复 handler 起始的 pop/astore、依选项处理空区间、monitor 和返回块，再插入 handler 前置块、合并基本块，最后处理多入口异常区间 | `ExceptionDeobfuscator`、`DeadCodeHelper` |
| 语句分解与 finally | 由 CFG 创建基本块语句、虚拟出口和初始根。按上游顺序识别循环、switch、if、顺序、catch、catch-all。识别 finally 会修改 CFG，随后重新建语句图，直到该轮不能再处理 finally | `DomHelper.graphToStatement`、`DomHelper.parseGraph`、`FinallyProcessor.iterateGraph` |
| 表达式与数据流 | 在结构化的方法内模拟操作数栈，将表达式放入语句。按分析需要构造 DirectGraph，保留共享的表达式列表。SSA 建立定义版本，SSAU 进一步区分使用位置，支撑有副作用表达式的内联判断 | `ExprProcessor`、`FlattenStatementsHelper`、`StackVarsProcessor`、`VarProcessor` |
| 方法重写 | 依次完成栈变量简化、循环和标签恢复、高级语法识别、作用域和变量声明。内层循环、主循环和末尾处理有不同的重启条件；每个 pass 的返回值由调用点解释 | `MethodProcessor.codeToJava`、`JavaPassLocation` |
| 整类还原与写出 | 在全部相关方法可用后处理捕获变量、成员访问和初始化器。写出时还会进行晚期 switch 等改写。先格式化正文和收集 tracer，再生成包含 imports 的类头，最后修正映射行数并写入结果 | `ClassesProcessor`、`ClassWriter`、`TextBuffer`、`BytecodeSourceMapper` |

## 方法内的调用顺序

1. 方法初始图保留 Java 的语句编号、子语句集合、异常边、标签归属和虚拟出口。单个无自环的块可以直接成为根的子语句；带自环的单块也需要进入 `GeneralStatement`。
2. `DomHelper.processStatement` 先按 do、switch、if、双块 sequence、catch、catch-all 的顺序试探并折叠候选。候选耗尽后，按强连通分量和后支配关系寻找子图，递归分解成功才替换父图中的节点。随后才走 force-all 候选、不可约图拆点和支配信息重算。父图、子图与失败处理的顺序按原调用点保留。
3. 结构分解成功后，降低 continue 标签、压缩 sequence、计算 monitor 标记并恢复 synchronized。`FinallyProcessor` 若改变 CFG，就从这份 CFG 重新执行整个 `parseGraph` 并传递前一轮的注释。直到 finally 稳定，才再识别 synchronized、移除其隐式 handler、构建内容标志并清理临时语句状态。
4. `ExprProcessor` 从字节码生成表达式。每轮先简化栈变量、建立变量版本，再尝试识别 ++/--。识别成功就重做这两步。之后处理遗漏的内联自增、按版本处理 invokedynamic 字符串拼接、构建 assert，再进入 `BEFORE_MAIN` 插件位置。
5. 主循环先清边。有循环的根进入内层循环，依次处理消除循环、增强循环、抽取循环、插件和合并 if；其中增强循环自身成功不会立即重启。回到外层后重新简化栈变量、计算变量版本、识别标签，继续处理次级表达式、交叉类型转换、模式匹配、switch、try 和单块内联。do-while 与无限循环返回的归并要等到此时。`MAIN_LOOP` 后才处理出口归并，静态初始化器跳过该步。
6. 主循环稳定后才简化 switch，必要时重新建立 switch 表达式与变量版本。然后调整返回类型、移除冗余 return、清理 synchronized 变量。经过 `AFTER_MAIN` 再确定变量声明，更新赋值、隐藏空 default 边、限定泛型链并规范类型转换。`AT_END` 之后才将可替换的 continue 改写为 break。类级处理和 writer 接收此结果。

方法的控制逻辑放在能看到上述调用顺序的地方。具体识别器只负责候选条件和它对应的图修改。这样可以在同一阶段比较改写前后的图，也能表达“成功后继续本轮”和“成功后重启外层”两种行为。

## 方法图的所有权

类文件、常量池和解码后的指令可以共享。一条指令从全方法序列进入基本块时共享同一个 `Arc<Instruction>`。上游显式克隆指令时创建新的指令对象。字节偏移、指令索引、算法赋予的整数编号和 Rust arena 句柄各自有独立用途。

根类工作上下文 `Cx` 持有 `Ir`。基本块、语句、语句边和共享表达式列表在它们各自的 arena 中有稳定身份。将节点从活跃图中移除时更新图成员和邻接关系，已有句柄仍能引用原对象。不同方法的块编号都可以从 1 开始，方法计数器与该方法的图一起保存。首次查找库类时，注解及其各个元素会在当前活动的方法计数器中取得表达式编号。库类缓存由工作上下文共享，同一类只解析一次。离开方法时恢复外层计数器。处理嵌套类或晚期访问另一方法时，使用该方法保存的计数器。只依赖图的算法借用 `&Ir` 或 `&mut Ir`，需要类路径、命名或会话选项的调用再借用相应上下文。

CFG、语句图和 DirectGraph 具有不同的边契约。

- CFG 的普通边有顺序并允许重复。条件跳转先记录跳转目标，再记录直落目标。switch 先记录 default，再按 case 顺序添加目标。异常边按 handler 去重，类型和受保护的块另外保存在有序的异常范围中。原始虚拟出口先登记返回块作为前驱，清理阶段才补上返回块的后继。
- 语句既有子语句，也有控制流。break、continue 和 finally-exit 边可以携带其归属的语句。修改一条边时，源、目的和标签归属必须与该阶段的上游操作同步。初始语句图之后还有结构分解与 finally 重建，其根节点不能直接交给 writer 生成最终源码。
- DirectGraph 是为数据流生成的视图。一个语句可以展平为多个直接节点，同一份表达式列表也可被直接节点和语句共同引用。SSA 的修改必须能被后续语句处理看到。

## 实现约定

- 类型、描述符、字节码和表达式采用有领域含义的结构或枚举。读取、筛选候选、类型推导和集合变换优先写成纯函数。显式循环适用于 DFS、工作队列、编号分配和需要重启的重写算法。保持候选发现的先后次序。
- 集合按使用方式选择。仅查找用 `FxHashMap`，保留插入顺序用 `IndexMap`，Java 值键的桶遍历可见时使用 `JHashMap`。默认身份哈希取决于 JVM 对象，Rust 句柄只承诺相同的身份关系；需要遍历身份集合时采用确定的顺序，并检查首次选中候选是否影响输出。对 Java 字符串排序时比较 UTF-16 单元。
- 常量池的字符串值保留原始 UTF-16 单元，标识符和描述符沿用框架的共享 UTF-8 接口。字面量与字符串哈希读取原始单元。输出的 token 位置、换行调整和源码映射使用 `TextBuffer` 的位置语义。
- 复用标准库和现有依赖处理 I/O、ZIP 压缩、运行时镜像、arena 和基本位运算。字节码规范化、异常保护范围、结构分解、类型合并、名称选择、括号和源码映射由对应的上游算法决定。匹配规则作用在语句和表达式上，主链无需解析 Java 或 Rust 源码。
- 方法解析失败在方法边界记录，上游允许跳过的可选属性保留缺失状态，类文件读取用 `io::Result`。取消应传回调用方。运行时的 Java 插件与宿主 JVM 的装载协议单独对待；已知插件通过语言选择、变量命名、方法和类级 pass 的对应位置接入。

## 库与自有实现的边界

| 操作 | 选择与原因 |
| --- | --- |
| 文件系统、ZIP/JAR、JDK 镜像 | 用标准库读取文件，`rawzip` 枚举 ZIP 中央目录的原始条目，`flate2` 解压 Deflate 数据，`jimage-rs` 读取 JDK 镜像。在 `StructContext` 保留自有类与库类的区别、类路径遮蔽顺序以及懒加载。 |
| class 文件、描述符、签名、指令 | 复用现有解码器。保留常量池索引、宽指令归一化、原字节偏移、跳转目标与异常表。JSR 展开使用上游的类型步进规则；后续表达式构建有独立的栈语义。 |
| lexer、`syn`、规则匹配 | 输入是 class 字节。`syn` 解析 Rust 源码。上游 `struct.match.MatchEngine` 的规则字符串描述待匹配的语句和表达式，适合在匹配器内实现这一小段语法。writer 直接在生成标识符时登记 token 和字符区间。 |
| 图、集合和编号 | 用 arena 提供稳定句柄。基本块普通边是有序多重边，异常范围独立于边；图的归并、后支配候选排序由移植代码控制。库可承载位集合与索引。对遍历会影响结果的 Java 值键表，`JHashMap` 保留 JDK 桶遍历、扩容、树化、树桶分裂与退化，以及 `put` 和 `computeIfAbsent` 的不同插入位置。树桶将红黑树与遍历链分开，迭代器删除可以使链头与树根不同。哈希和 Java 比较顺序相同、类名也无法区分时，用稳定的句柄或入表序号代替 JVM 身份哈希，此时两端遍历可能不同。 |
| 打印与映射 | 保留 `TextBuffer` 对 UTF-16 位置、换行组和 tracer 的处理。优先级、导入冲突以及字节码到源码行的映射在原有调用位置解决。 |

## 当前实现边界

[Java 方法入口](src/engine/method_processor.rs) `structured_statement_graph` 完成 `MethodProcessor` 中首次 `DomHelper.parseGraph` 调用。返回的 `StructuredMethod` 保留根语句、CFG 和方法计数器。没有保留 Code 的方法返回 `None`，无法分解的图返回方法级解析错误。调用 `initial_statement_graph` 可以取得折叠前的图，再按值调用 `structure` 继续。

[结构分解](src/decompiler/decompose/dom_helper.rs) 先识别六种简单语句，再用强连通分量、后支配和扩展后支配挑选单入口子区域。折叠时同步维护有序出入边、标签归属和异常覆盖；可归并节点耗尽时，按上游的条件尝试不可约图拆点和重算候选。分解成功后执行 continue 标签下移、顺序语句压缩和 synchronized 识别。

[DirectGraph](src/decompiler/flow/flatten.rs) 可从这一阶段的结构化语句树建立数据流视图。构图时登记语句对应的普通与 continue 目标，全部直接节点分配完成后连边。try 作用域收集内部节点的异常边；case 节点保留对应分支的表达式。结构分解产生的循环初始为无限循环。循环增强以后，普通入口与 continue 入口可能不同。例如计数循环从初始化进入，continue 流向步进表达式；增强 for 从可迭代对象进入，continue 流向循环变量。直接节点与语句共享实际存在的循环头表达式列表，计数循环缺少初始化时，直接图持有单独的空列表。不可达的非出口直接节点依照确定的创建顺序前置；上游使用含 JVM 对象身份散列的集合，这一小段遍历顺序可能随运行变化。

[`StructuredMethod::process_expressions`](src/engine/method_processor.rs) 在当前语句树上运行 [`ExprProcessor`](src/decompiler/expr_processor/driver.rs)。沿直接图的普通边传播操作数栈时，首次到达后继就复制其中的变量表达式；处理 catch 入口时从对应的异常变量重新建立栈。基本块把结果写入表达式列表，随后 if、switch 和 synchronized 从首块取回各自的头表达式。switch 头引用语句持有的分支标签。表达式的 Java 编号按构造和复制的先后顺序分配，与 arena 句柄分开。

[类节点](src/engine/class_nodes/load.rs) 根据已登记类的 InnerClasses 和 EnclosingMethod 建立父子关系。类节点保存匿名类的实际父类型，表达式构造 `new` 时通过同一份节点表查询。根类的 [ImportCollector](src/engine/import_collector.rs) 结合类路径、继承层次和当前类决定短名，动态常量展开和泛型类型名都经过这个入口。方法阶段差分直接使用同一 CFG，类节点与导入的差分另用已登记文件组成的类路径。

[根类准备](src/engine/class_processor.rs) 先建立该根的导入作用域，再从已有子类开始扫描 LambdaMetafactory 调用点，最后按类树顺序登记隐式名称。类节点以独立句柄保存；一次 invokedynamic 调用点分配一个节点，多个调用点可以共享合成名称，名字查找返回最后登记的节点。嵌套 lambda 保留在原类的子列表中，同时记录其实际 lambda 父节点。合成体和方法引用的区别由 owner 与目标方法的 synthetic 属性决定。

[稀疏变量版本分析](src/decompiler/sforms/mod.rs) 在同一套直接图传播规则上实现 SSA 和 SSAU。普通边传递分支出口状态，异常边传递保护区内可见的局部变量。普通 SSA 保留汇合点的来源版本；重编号按表达式里的指令对象登记映射，使 finally 能在 CFG 上识别等价的变量访问。SSAU 为读位置分配版本，记录使用关系、保护范围及存活集合，最后在版本图上计算支配关系。两次分析之间按原版遍历次序清除表达式上的版本号。

[finally 恢复](src/decompiler/finally/mod.rs) 每轮分析一个新的 catch-all handler。通过变量版本追踪异常的保存和重抛，再比较每个正常出口的指令、后继和异常保护关系。可以验证的重复清理块从 CFG 中删除；需要保留原控制流时，在 try 的入口和出口插入一个合成整型局部变量。每轮改写后从同一 CFG 重建语句树，保留方法计数器、方法描述符和累积注释。

[`expression_method`](src/engine/method_processor.rs) 串起解码、控制流清理、结构分解、finally 恢复和最终表达式构建。finally 稳定后重新识别 synchronized，移除它的异常处理器，记录树中是否有循环、switch 和 try/catch，清理临时边索引并压缩顺序语句。返回的表达式树保留对应 CFG 和合成变量。

`ExpressionMethod::simplify_stack_vars` 从这棵树开始。每轮先建立 SSA，在同一组 phi 信息下反复处理构造器、数组初始化、条件合并和三元表达式。清除版本并压缩顺序语句后，重新建立 SSAU。首轮沿构造器和 lambda 捕获参数标记需要保持 effectively final 的赋值，再沿直接图内联临时变量。内联要同时检查使用次数、支配关系、异常保护范围及来源表达式所依赖的变量版本。替换时合并字节码位置，迁移局部变量表信息，并更新仍存活的版本。两部分都稳定后，按原版再建一次 SSAU，处理最后一轮产生的冗余赋值。[栈变量处理入口](src/decompiler/stack/mod.rs)

表达式 arena 区分对象身份与结构相等。原版按身份替换子表达式的位置保留身份比较；在查找等价赋值目标、重复出现的匹配变量时使用相应表达式类型的相等规则。多个使用点需要独立副本时，按 Java 值键集合的迭代顺序复制，使表达式编号与求值顺序各自可核对。Java 1.4 类字面量沿用声明式语句树模式；匹配器只编译静态描述，每次匹配独立保存捕获值。[表达式操作](src/decompiler/exps/operations.rs) · [树模式匹配](src/structs/matcher.rs)

[`ExpressionMethod::set_var_versions`](src/decompiler/vars/versions.rs) 重新建立 SSA，把每组连通的 phi 版本归并到最小版本，再按 DirectGraph 普通边的广度优先顺序传播类型上下界。参数、异常变量、调试信息和各类表达式提供约束。只有已有下界上升时才重启本轮。收敛后根据变量槽与版本分配新编号。每个变量持有其方法类型表的句柄，整类处理中可同时查询多个方法里使用相同槽号的变量。

`ExpressionMethod::process_increments` 按上游顺序运行栈简化、类型推断和自增识别。识别成功时，下一轮把新编号经上一轮的映射追溯到原始槽。稳定后才尝试将块末的前缀自增移入后继 if 的条件。

[`pre_main_method`](src/engine/method_processor.rs) 接着按 class 版本处理字符串拼接，再恢复断言，到达 `BEFORE_MAIN`。拼接识别器从调用和 bootstrap recipe 收集有序操作数，按 UTF-16 单元保留常量片段，再构建左结合的字符串表达式。断言恢复根据类初始化字节码记录的字段识别保护条件，保留条件与消息的求值位置。接口可引用同一根类下已初始化 wrapper 的合成持有类。[字符串拼接](src/decompiler/concat.rs) · [断言恢复](src/decompiler/assertions.rs)

方法主循环的第一步通过 `ExpressionMethod::clean_up_edges` 重置边标志、删除不能直接跳出的 break/continue，并重新确定跳转归属的语句。随后 `eliminate_loops` 按后序查找与外层循环共享基本块入口的无限循环。只有在 break 标签数量和 continue 目标允许时才移除一层，随后压缩 sequence，并按上游在无 SSA 的上下文中重新简化语句。一次调用至多消除一个循环，成功后从合并循环的起点重新遍历。[边清理](src/decompiler/labels.rs) · [冗余循环](src/decompiler/loops/eliminate.rs)

循环增强按后序检查入口条件，再依次尝试迭代器、数组和计数循环。识别器检查变量槽、版本、使用位置和异常保护区，成功后将表达式移到循环头并转移字节码范围。迭代器子类型通过已登记的类路径解析。循环抽取移动可离开循环的分支，同时改写对应的边与闭包。抽取成功后，`ExpressionMethod::merge_loops` 回到循环消除；条件合并也会重启这一内层循环。Java 的后测试循环识别发生在外层主循环的后续阶段。[循环增强](src/decompiler/loops/enhance.rs) · [增强 for](src/decompiler/loops/foreach.rs) · [循环抽取](src/decompiler/loops/extract.rs)

`ExpressionMethod::identify_main_loop_labels` 从每轮主循环的边清理开始，运行内层合并、重新简化栈变量并更新变量版本，再依据各分支的下一条语句确定哪些跳转需要显式标签。原版在同样大小的候选边组之间按 JVM 对象身份散列遍历来选择。Rust 对这种平局按发现顺序选择。[标签识别](src/decompiler/labels/identify.rs)

次级表达式改写在标签确定后运行。先尝试消除空 then 分支，再按原版的先后次序处理逻辑取反、浮点比较、三元式、复合赋值与装箱。某些改写只改变强制类型转换或装箱的写出标志；调用方是否重启由改写函数的返回值决定。[次级表达式](src/decompiler/secondary/mod.rs)

交叉类型转换检查方法参数的泛型上界和赋值变量在整棵树中的使用位置。合并时将具体类放在接口之前，保留各类型表达式的身份，并标记需要写成 `var` 的局部变量。次级表达式或交叉转换有改动时，`ExpressionMethod::prepare_pattern_matching` 都从边清理重新开始。两者稳定后的树是原版进入 `instanceof` 模式匹配的位置，此时变量声明仍待后续阶段确定。[交叉类型转换](src/decompiler/intersection.rs) · [方法主循环](src/engine/method_processor.rs)

模式恢复先确定布尔条件在各分支上最后一个必定求值的表达式，再检查分支的唯一前驱、源表达式能否重复使用，以及绑定的局部变量在前驱中是否已经赋值。记录模式按组件访问器的顺序恢复嵌套绑定。成功后，`ExpressionMethod::prepare_switches` 从主循环的边清理重新开始；布尔条件的数据流只在匹配成功的路径引入模式变量。[条件模式](src/decompiler/patterns/mod.rs) · [记录解构](src/decompiler/patterns/record.rs) · [条件数据流](src/decompiler/sforms/process_expr.rs)

同一轮主循环会先恢复由 `SwitchBootstraps` 编译的模式标签和守卫，再检查各个离开 switch 的分支是否向同一变量赋值。恢复出的 switch 表达式持有原语句的 arena 句柄，各分支上的赋值改为 `yield`。下一轮的变量分析继续遍历承载分支的语句。标签类型无法与选择器合并时，变量分析会返回带选择器类型的错误。[模式 switch](src/decompiler/switches/patterns/mod.rs) · [switch 表达式](src/decompiler/switches/expression.rs)

资源恢复根据 class 版本检查 finally 清理或受抑制异常的 catch 结构，通过类路径确认 `close()V` 的声明类型实现了 `AutoCloseable`。正常出口的清理都通过检查以后，再将初始化表达式移到 try 头部。嵌套资源合并保留声明顺序。单块内联在资源恢复稳定后运行，只能跨过原版允许的保护区和标签作用域。[try-with-resources](src/decompiler/resources/mod.rs) · [单块内联](src/decompiler/inline_blocks.rs)

主循环在内联完成后才尝试恢复 `do … while` 以及从无限循环提取返回。普通方法可以把符合保护区和标签条件的 break 合并为返回；静态初始化器跳过该步骤。每次成功的改写都回到主循环开头。`main_loop_method` 将方法字节码处理到内置 Java 流程的 `MainLoopEnd`。消除嵌套循环时，Java 将被移走的标签边从身份散列集合逐个追加到外层循环的前驱表，同一批边的内部顺序会随 JVM 运行变化。Rust 保留发现顺序。[晚期循环](src/decompiler/loops/late.rs) · [出口合并](src/decompiler/exits.rs) · [主循环](src/engine/method_processor.rs)

类包装器先按声明顺序分析整张方法表，再依次处理各方法。整个类处理完后，类节点才公布包装器；这决定了枚举 switch 能在何时读取合成映射表。枚举恢复通过已发布方法的真实语句树和按需构建的直接图查找字段赋值。字符串 switch 按原版识别由哈希分派、字符串相等检查、空值路径及第二级 switch 组成的结构，保留同一哈希桶中各字符串的分支。[类包装器](src/engine/class_wrapper.rs) · [枚举恢复](src/decompiler/switches/enums.rs) · [字符串恢复](src/decompiler/switches/strings/mod.rs)

`after_main_method` 接着按方法返回类型调整常量，移除隐式路径末尾的空返回，再处理次级表达式和同步锁。移除返回时将对应字节码位置并入方法的虚拟出口；用装箱调用的结果充当锁时，调用必须保留装箱。该入口抵达 Java 插件钩子 `AFTER_MAIN`，变量声明的位置和名称由此后的阶段确定。[方法处理](src/engine/method_processor.rs) · [返回与同步锁](src/decompiler/post_process.rs)

变量处理器与方法包装器共享生命周期。每轮 SSA 只替换版本、上下界和槽号来源；名字、声明和局部变量表属于方法。声明阶段从接收者和参数开始，按 JVM 槽宽保留参数名，查找可合并的变量后再沿语句树确定共同作用域。能在首次赋值处声明的变量复用左操作数，其余在第一次读取前插入声明。放置后再运行一轮合并，传播调试信息，标记重复赋值，检查分支及嵌套方法中同时可见的重名。尚无类型下界的声明可以保留空的原始类型，查询有效类型时按上游顺序回到处理器。[`defined_method`](src/engine/method_processor.rs) · [变量合并与声明](src/decompiler/vars/definitions/mod.rs) · [命名作用域](src/decompiler/vars/definitions/clashes.rs)

变量声明确定后，重新检查复合赋值，隐藏空 default 的退出边，再沿调用链推断泛型实参。调用保存解析到的实际方法、类型代换和接收者类型。类型参数即使同名，也要保留来自不同声明的身份。嵌套强制转换在此之后归并。到达 `AT_END` 后，最后一次标签改写才把符合条件的 continue 换成 break；方法树保留原标签信息供写出。最终诊断在锁定导入表的作用域中查看变量声明、断言字段与残留的控制表达式。内置 Java 方法入口为 `code_to_java`，根类使用 `initialize_java_wrappers` 处理全部方法。[泛型调用链](src/decompiler/generic_chains.rs) · [最终标签](src/decompiler/labels/finish.rs) · [最终诊断](src/decompiler/expr_processor/oddities.rs)

类包装器为 abstract 和 native 方法保留参数槽，并在每个成功方法返回后避开同名字段。启用局部变量表时，包装器用原槽查找调试名，再次检查变量作用域。内置 identity、JAD、Tiny 命名策略按原方法缓存参数名，局部类、匿名类及 lambda 方法可以继承外层策略状态。Tiny 开启参数重命名时，对只有调试条目且缺少类型的参数，上游会在该方法中止命名；Rust 保留对应的方法级错误。[变量状态](src/decompiler/vars/processor.rs) · [命名策略](src/decompiler/vars/naming/mod.rs)

根类及其子类的所有方法包装器发布后，`process_class` 才处理嵌套类。它先从构造器和调用点归并合成参数，沿外层方法继承变量名、调试类型和来源，再放置局部类声明。每次替换既保留所属方法的变量槽，又从当前上下文分配表达式编号。最后识别旧版字节码用于跨类访问的合成方法，重写调用并隐藏已经消除的成员。写出阶段可以继续使用同一份方法体、导入表和已经建立的直接图。[类级入口](src/engine/class_processor.rs) · [捕获参数](src/engine/nested/captures.rs) · [局部类声明](src/engine/nested/declaration.rs) · [合成访问器](src/engine/nested/member_access.rs)

常量写出保留 JVM 类型、UTF-16 字符、字节码映射和源码 token。浮点数先按 JDK 17 的十进制转换规则求值，再应用 Vineflower 的截短和符号常量恢复。宽整数运算由 `num-bigint` 提供；普通转换走固定宽度路径。注解元素和方法里的常量共用同一入口。[字面量写出](src/decompiler/exps/literal/mod.rs) · [十进制转换](src/util/java_decimal.rs)

写出普通类前，`prepare_class_for_writing` 逐个恢复当前方法及其计数器，执行末轮 switch 和 if 改写。随后按声明和执行顺序抽取静态初始化器与各构造器共有的实例初始化器，处理合成构造器、Java 1.4 类字面量和 enum 成员。最后检查 record 的规范构造器并重新核对变量重名。抽出的右值保留原表达式身份，后续写字段仍能访问原字节码位置。[写出准备](src/engine/class_writer/mod.rs) · [初始化器](src/engine/class_writer/initializers.rs)

普通类的声明头从类节点、父类和所在接口取修饰符，并在使用泛型签名前用擦除后的描述符校验。record 组件按组件、访问方法、规范构造器参数的次序查找声明注解，再按 JVM type path 写入类型注解。已写标志属于解析出的注解对象，重复写同一对象时沿用其状态。类型、类名和组件名写入同一份 `TextBuffer`，换行之后仍可定位对应 token。[类声明](src/engine/class_writer/declaration.rs) · [record 组件](src/engine/class_writer/record_components.rs) · [类型注解](src/engine/class_writer/type_annotations.rs)

包描述符和模块描述符可以直接从已准备的根类写出。包注解先登记导入，再把导入写在包声明之后。模块先生成正文，随后在正文前写入导入。两条路径和普通声明共用注解值、类型 token 和换行组。[元数据写出](src/engine/class_writer/metadata.rs) · [写出入口](src/engine/class_processor.rs)

普通根类通过 `process_class` 和 `class_processor::write_class` 写成完整的 Java 编译单元。表达式在原有 IR 对象上处理强制转换、泛型实参及装箱，语句树负责标签、跳转、作用域和块换行。局部类、匿名类、方法引用和 lambda 递归使用所属的类或方法包装器。各字段和方法先生成独立的正文，再把字节码映射归到原方法；汇总正文和导入后，源码映射器才补入类头行数。写完只释放根类包装器，其他根类仍可查询其子类构造器。[表达式写出](src/decompiler/exps/write/mod.rs) · [语句写出](src/decompiler/stats/write/mod.rs) · [成员写出](src/engine/class_writer/class.rs) · [源码行映射](src/engine/bytecode_source_mapper.rs)

方法处理失败时仍可写出同一类的其他成员。错误注释和剩余字节码列表遵循原选项；异常说明记录 Rust 返回的原因。上游 JVM 异常的类名和 Java 栈帧会与 Rust 的诊断文本不同。[错误写出](src/engine/class_writer/method_errors.rs)

`RuntimeImage::open` 将模块化 JDK 的每个模块作为独立库登记，按 JRT 的目录遍历和模块描述符顺序提供条目。随仓库固定的 `jimage-rs` 复用内存映射和资源索引，普通资源直接借用映射中的字节。读取压缩资源时，按镜像头的字节序逐层解码 ZIP 或 `compact-cp`。后者从镜像的共享字符串表重建 class 常量池，直接复制 Modified UTF-8 字节，保留 JVM 字符串的原始表示。[运行时类路径](src/engine/context_source/runtime.rs) · [镜像读取器及版本来源](vendor/jimage-rs/README.md)

`StructContext::add_file` 根据文件后缀和 ZIP 结束记录登记目录、归档或单文件。重新载入上下文时再次扫描目录及其子归档。ZIP 保留中央目录顺序和重复条目，按 Java 的规则解释多版本路径。单个 class 文件在预读内部名称和正式解析时使用同一上下文的注解表达式计数器。直接读取缺失资源或目录时，Rust 的 `ContextSource` 返回 `Ok(None)`。Java 的目录源打开这些路径时抛出 I/O 异常，ZIP 源读取缺失条目时抛出空引用异常，读取显式目录条目时返回空流。正常登记按已有条目读取类和资源。[文件登记](src/structs/struct_context.rs)

同步区扩展有一处有意的终止条件。当共享后继的首个前驱来自另一保护区，上游可能反复向已覆盖的区间追加同一块。如果本轮既不会新增覆盖关系、也不会增加异常边或移动指令，Rust 跳过这个候选，继续检查其他区间。

断言 IR 允许顶层条件为空，用来表达 `assert false`。上游递归剥离断言字段时还可能把空引用写进 `&&` 的操作数。Rust 的二元表达式要求两个有效操作数，遇到后一种形状会在断言恢复阶段返回方法级错误。当前真实 class 对照尚未触发这条路径。

## Kotlin 插件

同一个输入单元可以含有 Java 和 Kotlin 根类。CLI 默认装载 Kotlin 插件，库调用方通过 `Options::decompile_kotlin` 选择是否装载。入口按原版在选输出扩展名、处理根类和写出类时调用语言选择器。Kotlin 插件读取 JVM 注解中的 `kotlin.Metadata`。单独开启元数据导出时，解析出的成员关系也可供库调用查询。名称解析保留 JVM 的字符串表、UTF-16 范围和预定义名字。编译好的 protobuf 类型随 Rust 项目提交，普通构建无需安装 Kotlin 编译器或 protoc。[语言入口](src/kotlin/mod.rs) · [元数据](src/kotlin/metadata/mod.rs) · [模式生成工具](tools/kotlin-schema)

编译单元共享一份成员表。属性的字段、getter 和 setter 引用同一声明，companion 的静态入口保留原始 JVM 方法身份。解析中途失败时，先前已关联的成员仍可供后续查找。Kotlin 方法沿原插件顺序复用 JVM 指令解码、CFG、finally 和变量分析，再替换对应的语句与表达式。语言专属信息附着在 arena 的实际节点上，子表达式在普通写出入口也能分派到正确的语言实现。[成员绑定](src/kotlin/members/mod.rs) · [方法流水线](src/kotlin/passes/mod.rs) · [表达式与语句](src/kotlin/body/mod.rs)

类级写出先抽取初始化器，处理 enum 与 companion，再写主构造器、属性、函数和嵌套类。主构造器已消费的 super 调用从后续块里移除。默认实参读取真实 JVM 桥方法的位掩码，注解构造器则读取成员的 `AnnotationDefault`。正文与字段初始化器保留字节码位置，复用 `TextBuffer` 完成排版、token 归属和源码行映射。类头在正文确定所有导入后生成。表达式列表写出时，上游再次根据最后初始化的包装器所属类选择语言。这个类与当前写出节点分别存于根类会话，嵌套类元数据的加载时机与分号规则都依赖这一区别。[类写出](src/kotlin/writer/class.rs) · [成员写出](src/kotlin/member_writer/mod.rs) · [文件头](src/kotlin/writer/header.rs)

## 核对实现

真实输入的检查点依次为解码序列、原始 CFG、共同清理后的 CFG、Java 异常整理后的 CFG、初始语句图、结构分解、数据流和最终源码。中间结果应按其自身的语义比较。例如 switch 目标比较有序列表，异常表比较区间、处理器和捕获类型，源码比较沿用上游的换行及外侧空白规则。

出现差异时，先找到同一个方法中最早不同的检查点，再核对产生该状态的 Java 调用。重编译和执行能检查语义，也是分析上游本身无法重编译的输出时的补充证据。golden、案例名称和历史 Rust 输出不参与生产代码的决策。
