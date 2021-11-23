Add to llvm-13 repo to sources.list:

```bash
sudo vim /etc/apt/sources.list
```

Insert these lines:

```log
deb http://apt.llvm.org/focal/ llvm-toolchain-focal-13 main
deb-src http://apt.llvm.org/focal/ llvm-toolchain-focal-13 main
```

Install llvm and lld version 13:

```bash
sudo apt-get update
sudo apt-get install llvm-13 lld-13 clang-13
```
