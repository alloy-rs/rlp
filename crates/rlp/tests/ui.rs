//! Compile-fail coverage for derive diagnostics.

#[test]
fn derive_compile_failures() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/ui/*.rs");
}
