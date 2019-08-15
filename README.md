# Setting things up

Make sure you have `make`, `mono`, and `wget`

```
mono -V
which wget
```

## Set up dafny (and boogie, z3)

*From the project root*, run:

```
./tools/install-dafny.sh
```

This will download and compile boogie, veri-dafny, z3.

You can run veri-dafny with `./.dafny/bin/dafny`, the Makefile will use veri-dafny by default
