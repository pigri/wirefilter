fn main() {
    println!("cargo::rerun-if-changed=src/tests.c");
    #[cfg(unix)]
    cc::Build::new()
        .include("../../include")
        .file("src/tests.c")
        .warnings(true)
        .extra_warnings(true)
        .warnings_into_errors(true)
        .compile("wirefilter_ffi_ctests");
}
