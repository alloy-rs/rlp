use std::{env, fs, path::Path};

fn write_seed(corpus: &Path, name: &str, bytes: &[u8]) {
    fs::write(corpus.join(name), bytes).expect("failed to write RLP fuzz seed");
}

fn list(items: impl IntoIterator<Item = Vec<u8>>) -> Vec<u8> {
    let payload: Vec<_> = items.into_iter().flatten().collect();
    let mut out = Vec::new();
    match payload.len() {
        len @ 0..=55 => out.push(0xc0 + len as u8),
        len => {
            let length = len.to_be_bytes();
            let length = length.iter().skip_while(|byte| **byte == 0).copied().collect::<Vec<_>>();
            out.push(0xf7 + length.len() as u8);
            out.extend(length);
        }
    }
    out.extend(payload);
    out
}

fn long_string(byte: u8) -> Vec<u8> {
    let mut string = vec![0xb8, 56];
    string.extend(std::iter::repeat(byte).take(56));
    string
}

fn main() {
    let corpus = Path::new(&env::var("CARGO_MANIFEST_DIR").expect("missing manifest directory"))
        .join("corpus/list_decode_differential");
    fs::create_dir_all(&corpus).expect("failed to create RLP fuzz corpus");

    write_seed(&corpus, "empty-list", &[0xc0]);
    write_seed(&corpus, "small-strings", &list([vec![0x80], vec![0x00], vec![0x7f]]));
    write_seed(
        &corpus,
        "nested-lists",
        &list([list([vec![0x80], list([vec![0x01]])]), vec![0xc0]]),
    );
    write_seed(&corpus, "long-string", &list([long_string(0xaa)]));
    write_seed(&corpus, "many-items", &list(std::iter::repeat(vec![0x80]).take(128)));

    let mut deeply_nested = vec![0x80];
    for _ in 0..64 {
        deeply_nested = list([deeply_nested]);
    }
    write_seed(&corpus, "deeply-nested", &list([deeply_nested]));

    // Boundary and canonicality failures make sure both decoders take the same error path.
    write_seed(&corpus, "truncated-long-list", &[0xf8]);
    write_seed(&corpus, "noncanonical-long-list", &[0xf8, 0x01, 0x80]);
    write_seed(&corpus, "noncanonical-single-byte", &[0xc2, 0x81, 0x00]);
    write_seed(&corpus, "truncated-item", &[0xc2, 0x82]);
}
