fn main() {
    cxx_build::bridge("src/lib.rs") // returns a cc::Build
        //.compiler("clang-13")
        .flag_if_supported("-std=c++11")
        //.flag_if_supported("-flto")
        .compile("cxxbridge-demo");

    println!("cargo:rerun-if-changed=src/lib.rs");
    println!("cargo:rerun-if-changed=include/demo.h");
}
