//! `code.CodeConstants`: variable type tags, access flags, instruction
//! groups, constant pool tags and the JVM opcodes.

// ----------------------------------------------------------------------
// VARIABLE TYPES
// ----------------------------------------------------------------------

pub const TYPE_BYTE: i32 = 0;
pub const TYPE_CHAR: i32 = 1;
pub const TYPE_DOUBLE: i32 = 2;
pub const TYPE_FLOAT: i32 = 3;
pub const TYPE_INT: i32 = 4;
pub const TYPE_LONG: i32 = 5;
pub const TYPE_SHORT: i32 = 6;
pub const TYPE_BOOLEAN: i32 = 7;
pub const TYPE_OBJECT: i32 = 8;
pub const TYPE_ADDRESS: i32 = 9;
pub const TYPE_VOID: i32 = 10;
pub const TYPE_ANY: i32 = 11;
pub const TYPE_GROUP2EMPTY: i32 = 12;
pub const TYPE_NULL: i32 = 13;
pub const TYPE_NOTINITIALIZED: i32 = 14;
pub const TYPE_BYTECHAR: i32 = 15;
pub const TYPE_SHORTCHAR: i32 = 16;
pub const TYPE_UNKNOWN: i32 = 17;
pub const TYPE_GENVAR: i32 = 18;

// ----------------------------------------------------------------------
// ACCESS FLAGS
// ----------------------------------------------------------------------

pub const ACC_PUBLIC: i32 = 0x0001;
pub const ACC_PRIVATE: i32 = 0x0002;
pub const ACC_PROTECTED: i32 = 0x0004;
pub const ACC_STATIC: i32 = 0x0008;
pub const ACC_FINAL: i32 = 0x0010;
pub const ACC_SYNCHRONIZED: i32 = 0x0020;
pub const ACC_OPEN: i32 = 0x0020;
pub const ACC_TRANSITIVE: i32 = 0x0020;
pub const ACC_STATIC_PHASE: i32 = 0x0040; // modules
pub const ACC_NATIVE: i32 = 0x0100;
pub const ACC_ABSTRACT: i32 = 0x0400;
pub const ACC_STRICT: i32 = 0x0800;
pub const ACC_VOLATILE: i32 = 0x0040;
pub const ACC_BRIDGE: i32 = 0x0040;
pub const ACC_TRANSIENT: i32 = 0x0080;
pub const ACC_VARARGS: i32 = 0x0080;
pub const ACC_SYNTHETIC: i32 = 0x1000;
pub const ACC_ANNOTATION: i32 = 0x2000;
pub const ACC_ENUM: i32 = 0x4000;
pub const ACC_MANDATED: i32 = 0x8000;
pub const ACC_MODULE: i32 = 0x8000;

// ----------------------------------------------------------------------
// CLASS FLAGS
// ----------------------------------------------------------------------

pub const ACC_SUPER: i32 = 0x0020;
pub const ACC_INTERFACE: i32 = 0x0200;

// ----------------------------------------------------------------------
// INSTRUCTION GROUPS
// ----------------------------------------------------------------------

pub const GROUP_GENERAL: i32 = 1;
pub const GROUP_JUMP: i32 = 2;
pub const GROUP_SWITCH: i32 = 3;
pub const GROUP_INVOCATION: i32 = 4;
pub const GROUP_FIELDACCESS: i32 = 5;
pub const GROUP_RETURN: i32 = 6;

// ----------------------------------------------------------------------
// POOL CONSTANTS
// ----------------------------------------------------------------------

pub const CONSTANT_UTF8: i32 = 1;
pub const CONSTANT_INTEGER: i32 = 3;
pub const CONSTANT_FLOAT: i32 = 4;
pub const CONSTANT_LONG: i32 = 5;
pub const CONSTANT_DOUBLE: i32 = 6;
pub const CONSTANT_CLASS: i32 = 7;
pub const CONSTANT_STRING: i32 = 8;
pub const CONSTANT_FIELDREF: i32 = 9;
pub const CONSTANT_METHODREF: i32 = 10;
pub const CONSTANT_INTERFACEMETHODREF: i32 = 11;
pub const CONSTANT_NAMEANDTYPE: i32 = 12;
pub const CONSTANT_METHODHANDLE: i32 = 15;
pub const CONSTANT_METHODTYPE: i32 = 16;
pub const CONSTANT_DYNAMIC: i32 = 17;
pub const CONSTANT_INVOKEDYNAMIC: i32 = 18;
pub const CONSTANT_MODULE: i32 = 19;
pub const CONSTANT_PACKAGE: i32 = 20;

// ----------------------------------------------------------------------
// MethodHandle reference_kind values
// ----------------------------------------------------------------------

pub const CONSTANT_METHODHANDLE_REF_GETFIELD: i32 = 1;
pub const CONSTANT_METHODHANDLE_REF_GETSTATIC: i32 = 2;
pub const CONSTANT_METHODHANDLE_REF_PUTFIELD: i32 = 3;
pub const CONSTANT_METHODHANDLE_REF_PUTSTATIC: i32 = 4;
pub const CONSTANT_METHODHANDLE_REF_INVOKEVIRTUAL: i32 = 5;
pub const CONSTANT_METHODHANDLE_REF_INVOKESTATIC: i32 = 6;
pub const CONSTANT_METHODHANDLE_REF_INVOKESPECIAL: i32 = 7;
pub const CONSTANT_METHODHANDLE_REF_NEWINVOKESPECIAL: i32 = 8;
pub const CONSTANT_METHODHANDLE_REF_INVOKEINTERFACE: i32 = 9;

// ----------------------------------------------------------------------
// VM OPCODES
// ----------------------------------------------------------------------

pub const OPC_NOP: i32 = 0;
pub const OPC_ACONST_NULL: i32 = 1;
pub const OPC_ICONST_M1: i32 = 2;
pub const OPC_ICONST_0: i32 = 3;
pub const OPC_ICONST_1: i32 = 4;
pub const OPC_ICONST_2: i32 = 5;
pub const OPC_ICONST_3: i32 = 6;
pub const OPC_ICONST_4: i32 = 7;
pub const OPC_ICONST_5: i32 = 8;
pub const OPC_LCONST_0: i32 = 9;
pub const OPC_LCONST_1: i32 = 10;
pub const OPC_FCONST_0: i32 = 11;
pub const OPC_FCONST_1: i32 = 12;
pub const OPC_FCONST_2: i32 = 13;
pub const OPC_DCONST_0: i32 = 14;
pub const OPC_DCONST_1: i32 = 15;
pub const OPC_BIPUSH: i32 = 16;
pub const OPC_SIPUSH: i32 = 17;
pub const OPC_LDC: i32 = 18;
pub const OPC_LDC_W: i32 = 19;
pub const OPC_LDC2_W: i32 = 20;
pub const OPC_ILOAD: i32 = 21;
pub const OPC_LLOAD: i32 = 22;
pub const OPC_FLOAD: i32 = 23;
pub const OPC_DLOAD: i32 = 24;
pub const OPC_ALOAD: i32 = 25;
pub const OPC_ILOAD_0: i32 = 26;
pub const OPC_ILOAD_1: i32 = 27;
pub const OPC_ILOAD_2: i32 = 28;
pub const OPC_ILOAD_3: i32 = 29;
pub const OPC_LLOAD_0: i32 = 30;
pub const OPC_LLOAD_1: i32 = 31;
pub const OPC_LLOAD_2: i32 = 32;
pub const OPC_LLOAD_3: i32 = 33;
pub const OPC_FLOAD_0: i32 = 34;
pub const OPC_FLOAD_1: i32 = 35;
pub const OPC_FLOAD_2: i32 = 36;
pub const OPC_FLOAD_3: i32 = 37;
pub const OPC_DLOAD_0: i32 = 38;
pub const OPC_DLOAD_1: i32 = 39;
pub const OPC_DLOAD_2: i32 = 40;
pub const OPC_DLOAD_3: i32 = 41;
pub const OPC_ALOAD_0: i32 = 42;
pub const OPC_ALOAD_1: i32 = 43;
pub const OPC_ALOAD_2: i32 = 44;
pub const OPC_ALOAD_3: i32 = 45;
pub const OPC_IALOAD: i32 = 46;
pub const OPC_LALOAD: i32 = 47;
pub const OPC_FALOAD: i32 = 48;
pub const OPC_DALOAD: i32 = 49;
pub const OPC_AALOAD: i32 = 50;
pub const OPC_BALOAD: i32 = 51;
pub const OPC_CALOAD: i32 = 52;
pub const OPC_SALOAD: i32 = 53;
pub const OPC_ISTORE: i32 = 54;
pub const OPC_LSTORE: i32 = 55;
pub const OPC_FSTORE: i32 = 56;
pub const OPC_DSTORE: i32 = 57;
pub const OPC_ASTORE: i32 = 58;
pub const OPC_ISTORE_0: i32 = 59;
pub const OPC_ISTORE_1: i32 = 60;
pub const OPC_ISTORE_2: i32 = 61;
pub const OPC_ISTORE_3: i32 = 62;
pub const OPC_LSTORE_0: i32 = 63;
pub const OPC_LSTORE_1: i32 = 64;
pub const OPC_LSTORE_2: i32 = 65;
pub const OPC_LSTORE_3: i32 = 66;
pub const OPC_FSTORE_0: i32 = 67;
pub const OPC_FSTORE_1: i32 = 68;
pub const OPC_FSTORE_2: i32 = 69;
pub const OPC_FSTORE_3: i32 = 70;
pub const OPC_DSTORE_0: i32 = 71;
pub const OPC_DSTORE_1: i32 = 72;
pub const OPC_DSTORE_2: i32 = 73;
pub const OPC_DSTORE_3: i32 = 74;
pub const OPC_ASTORE_0: i32 = 75;
pub const OPC_ASTORE_1: i32 = 76;
pub const OPC_ASTORE_2: i32 = 77;
pub const OPC_ASTORE_3: i32 = 78;
pub const OPC_IASTORE: i32 = 79;
pub const OPC_LASTORE: i32 = 80;
pub const OPC_FASTORE: i32 = 81;
pub const OPC_DASTORE: i32 = 82;
pub const OPC_AASTORE: i32 = 83;
pub const OPC_BASTORE: i32 = 84;
pub const OPC_CASTORE: i32 = 85;
pub const OPC_SASTORE: i32 = 86;
pub const OPC_POP: i32 = 87;
pub const OPC_POP2: i32 = 88;
pub const OPC_DUP: i32 = 89;
pub const OPC_DUP_X1: i32 = 90;
pub const OPC_DUP_X2: i32 = 91;
pub const OPC_DUP2: i32 = 92;
pub const OPC_DUP2_X1: i32 = 93;
pub const OPC_DUP2_X2: i32 = 94;
pub const OPC_SWAP: i32 = 95;
pub const OPC_IADD: i32 = 96;
pub const OPC_LADD: i32 = 97;
pub const OPC_FADD: i32 = 98;
pub const OPC_DADD: i32 = 99;
pub const OPC_ISUB: i32 = 100;
pub const OPC_LSUB: i32 = 101;
pub const OPC_FSUB: i32 = 102;
pub const OPC_DSUB: i32 = 103;
pub const OPC_IMUL: i32 = 104;
pub const OPC_LMUL: i32 = 105;
pub const OPC_FMUL: i32 = 106;
pub const OPC_DMUL: i32 = 107;
pub const OPC_IDIV: i32 = 108;
pub const OPC_LDIV: i32 = 109;
pub const OPC_FDIV: i32 = 110;
pub const OPC_DDIV: i32 = 111;
pub const OPC_IREM: i32 = 112;
pub const OPC_LREM: i32 = 113;
pub const OPC_FREM: i32 = 114;
pub const OPC_DREM: i32 = 115;
pub const OPC_INEG: i32 = 116;
pub const OPC_LNEG: i32 = 117;
pub const OPC_FNEG: i32 = 118;
pub const OPC_DNEG: i32 = 119;
pub const OPC_ISHL: i32 = 120;
pub const OPC_LSHL: i32 = 121;
pub const OPC_ISHR: i32 = 122;
pub const OPC_LSHR: i32 = 123;
pub const OPC_IUSHR: i32 = 124;
pub const OPC_LUSHR: i32 = 125;
pub const OPC_IAND: i32 = 126;
pub const OPC_LAND: i32 = 127;
pub const OPC_IOR: i32 = 128;
pub const OPC_LOR: i32 = 129;
pub const OPC_IXOR: i32 = 130;
pub const OPC_LXOR: i32 = 131;
pub const OPC_IINC: i32 = 132;
pub const OPC_I2L: i32 = 133;
pub const OPC_I2F: i32 = 134;
pub const OPC_I2D: i32 = 135;
pub const OPC_L2I: i32 = 136;
pub const OPC_L2F: i32 = 137;
pub const OPC_L2D: i32 = 138;
pub const OPC_F2I: i32 = 139;
pub const OPC_F2L: i32 = 140;
pub const OPC_F2D: i32 = 141;
pub const OPC_D2I: i32 = 142;
pub const OPC_D2L: i32 = 143;
pub const OPC_D2F: i32 = 144;
pub const OPC_I2B: i32 = 145;
pub const OPC_I2C: i32 = 146;
pub const OPC_I2S: i32 = 147;
pub const OPC_LCMP: i32 = 148;
pub const OPC_FCMPL: i32 = 149;
pub const OPC_FCMPG: i32 = 150;
pub const OPC_DCMPL: i32 = 151;
pub const OPC_DCMPG: i32 = 152;
pub const OPC_IFEQ: i32 = 153;
pub const OPC_IFNE: i32 = 154;
pub const OPC_IFLT: i32 = 155;
pub const OPC_IFGE: i32 = 156;
pub const OPC_IFGT: i32 = 157;
pub const OPC_IFLE: i32 = 158;
pub const OPC_IF_ICMPEQ: i32 = 159;
pub const OPC_IF_ICMPNE: i32 = 160;
pub const OPC_IF_ICMPLT: i32 = 161;
pub const OPC_IF_ICMPGE: i32 = 162;
pub const OPC_IF_ICMPGT: i32 = 163;
pub const OPC_IF_ICMPLE: i32 = 164;
pub const OPC_IF_ACMPEQ: i32 = 165;
pub const OPC_IF_ACMPNE: i32 = 166;
pub const OPC_GOTO: i32 = 167;
pub const OPC_JSR: i32 = 168;
pub const OPC_RET: i32 = 169;
pub const OPC_TABLESWITCH: i32 = 170;
pub const OPC_LOOKUPSWITCH: i32 = 171;
pub const OPC_IRETURN: i32 = 172;
pub const OPC_LRETURN: i32 = 173;
pub const OPC_FRETURN: i32 = 174;
pub const OPC_DRETURN: i32 = 175;
pub const OPC_ARETURN: i32 = 176;
pub const OPC_RETURN: i32 = 177;
pub const OPC_GETSTATIC: i32 = 178;
pub const OPC_PUTSTATIC: i32 = 179;
pub const OPC_GETFIELD: i32 = 180;
pub const OPC_PUTFIELD: i32 = 181;
pub const OPC_INVOKEVIRTUAL: i32 = 182;
pub const OPC_INVOKESPECIAL: i32 = 183;
pub const OPC_INVOKESTATIC: i32 = 184;
pub const OPC_INVOKEINTERFACE: i32 = 185;
pub const OPC_INVOKEDYNAMIC: i32 = 186;
pub const OPC_NEW: i32 = 187;
pub const OPC_NEWARRAY: i32 = 188;
pub const OPC_ANEWARRAY: i32 = 189;
pub const OPC_ARRAYLENGTH: i32 = 190;
pub const OPC_ATHROW: i32 = 191;
pub const OPC_CHECKCAST: i32 = 192;
pub const OPC_INSTANCEOF: i32 = 193;
pub const OPC_MONITORENTER: i32 = 194;
pub const OPC_MONITOREXIT: i32 = 195;
pub const OPC_WIDE: i32 = 196;
pub const OPC_MULTIANEWARRAY: i32 = 197;
pub const OPC_IFNULL: i32 = 198;
pub const OPC_IFNONNULL: i32 = 199;
pub const OPC_GOTO_W: i32 = 200;
pub const OPC_JSR_W: i32 = 201;

pub const CLINIT_NAME: &str = "<clinit>";
pub const INIT_NAME: &str = "<init>";

/// JVMS 2.9.3 Signature Polymorphic Methods
mod signature_polymorphic {
    /// The access modes that also come as `<name>Acquire` and `<name>Release`.
    const BASE: [&str; 6] = [
        "compareAndExchange",
        "getAndSet",
        "getAndAdd",
        "getAndBitwiseOr",
        "getAndBitwiseAnd",
        "getAndBitwiseXor",
    ];

    /// `VAR_HANDLE_RETURN_POLYMORPHIC`: methods returning Object
    pub(super) fn var_handle_return_polymorphic(name: &str) -> bool {
        matches!(name, "get" | "getVolatile" | "getOpaque" | "getAcquire")
            || BASE.iter().any(|base| {
                matches!(name.strip_prefix(base), Some("" | "Acquire" | "Release"))
            })
    }

    /// `VAR_HANDLE_PARAMETER_POLYMORPHIC`: methods returning void or boolean,
    /// and every method above
    pub(super) fn var_handle_parameter_polymorphic(name: &str) -> bool {
        matches!(
            name,
            "set"
                | "setVolatile"
                | "setOpaque"
                | "setRelease"
                | "compareAndSet"
                | "weakCompareAndSetPlain"
                | "weakCompareAndSet"
                | "weakCompareAndSetAcquire"
                | "weakCompareAndSetRelease"
        ) || var_handle_return_polymorphic(name)
    }
}

pub fn is_signature_polymorphic(classname: &str, name: &str, check_return: bool) -> bool {
    if classname == "java/lang/invoke/MethodHandle" {
        return name == "invokeExact" || name == "invoke";
    }
    if classname == "java/lang/invoke/VarHandle" {
        return if check_return {
            signature_polymorphic::var_handle_return_polymorphic(name)
        } else {
            signature_polymorphic::var_handle_parameter_polymorphic(name)
        };
    }
    false
}

pub fn is_return_polymorphic(classname: &str, name: &str) -> bool {
    is_signature_polymorphic(classname, name, true)
}

pub fn are_parameters_polymorphic(classname: &str, name: &str) -> bool {
    is_signature_polymorphic(classname, name, false)
}
