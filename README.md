# vineflower-rs

YinMo19, Codex
---

> Disclaimer: This repository was developed by AI AGENT.
>
> The README you are reading now was handwritten by me; but the rest is not. You can refer to the more detailed [AI-generated documentation](GUIDE.md) for develop.

This is a Rust implementation of a `.jar -> .java` decompiler, rewritten in Rust based on [Vineflower](https://github.com/Vineflower/vineflower). I hope that using Rust will enable more efficient computation throughout the entire process.

Although we have not conducted extensive testing, we can currently say that this project has almost fully replicated Vineflower, with functionality that is nearly complete. 

In terms of performance, on my M4 Pro, the Rust CLI was about 4.5× as fast as Vineflower on Guava, 5.5× on Gson, and 2× on the Minecraft 26.3 client. Both tools produced identical files on all three inputs.

Pull requests are welcome. Feel free to use AI tools, but please write the PR description yourself and explain what you changed and why. Code quality matters most to me. I’ll review PRs when I have time.

Licenses and Dependencies
---
See [ABOUT.md](ABOUT.md) for details. We rewrote it based on the original Vineflower and retained the Apache 2.0 license.
