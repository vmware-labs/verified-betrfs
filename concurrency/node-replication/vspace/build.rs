fn main() {
    cxx_build::bridge("src/lib.rs") // returns a cc::Build
        .flag_if_supported("-std=c++11")
        .compile("cxxbridge-demo");

    println!("cargo:rerun-if-changed=src/lib.rs");
    println!("cargo:rerun-if-changed=include/demo.h");
}
