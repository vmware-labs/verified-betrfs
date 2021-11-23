sudo vim /etc/apt/sources.list

```
# 13
deb http://apt.llvm.org/focal/ llvm-toolchain-focal-13 main
deb-src http://apt.llvm.org/focal/ llvm-toolchain-focal-13 main
```

sudo apt-get update
sudo apt-get install llvm-13 lld-13