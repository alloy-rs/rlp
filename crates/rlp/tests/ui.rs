//! Compile-fail coverage for derive diagnostics.

#[cfg(feature = "derive")]
#[test]
fn derive_compile_failures() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/ui/*.rs");
}
