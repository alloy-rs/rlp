# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- `decode_full` function ([#23])

[#23]: https://github.com/alloy-rs/rlp/pull/23

## [0.3.7] - 2024-06-29

### Fixed

- Make `PayloadView` public ([#20])

[#20]: https://github.com/alloy-rs/rlp/pull/20

## [0.3.6] - 2024-06-29

### Added

- New `decode_raw` static methods to `Header` ([#18])

[#18]: https://github.com/alloy-rs/rlp/pull/18

## [0.3.5] - 2024-05-22

### Changed

- Improved `encode_fixed_size` performance ([#15])

[#15]: https://github.com/alloy-rs/rlp/pull/15

## [0.3.4] - 2023-12-22

### Added

- `PhantomData` and `PhantomPinned` support ([#11])

### Removed

- `smol_str` support ([#8])

[#8]: https://github.com/alloy-rs/rlp/pull/8
[#11]: https://github.com/alloy-rs/rlp/pull/11

## [0.3.3] - 2023-09-23

### Fixed

- `Ip{,v4,v6}Addr::decode` ([#7])

[#7]: https://github.com/alloy-rs/rlp/pull/7

## [0.3.2] - 2023-07-26

### Added

- `encode` function ([#5])

### Changed

- Inline derive macros' docs ([#3])

[#3]: https://github.com/alloy-rs/rlp/pull/3
[#5]: https://github.com/alloy-rs/rlp/pull/5

## [0.3.1] - 2023-07-13

### Fixed

- `length_of_length` for non 64-bit platforms ([#2])

[#2]: https://github.com/alloy-rs/rlp/pull/2

## [0.3.0] - 2023-07-12

### Added

- `arrayvec` feature with `Encodable` and `Decodable` implementations
- `smol_str` feature with `Encodable` and `Decodable` implementations
- New `decode_bytes` and `decode_str` static methods to `Header`
- `Ipv4Addr` and `Ipv6Addr` `Decodable` implementations
- A `Result` type alias for `core::result::Result<T, E = Error>`
- Re-exports for `::bytes`, `Bytes`, and `BytesMut`
- Support for generics in derive macros

### Changed

- Default `Encodable::length` implementation to use `Vec` instead of `BytesMut`
- `rlp_list_header`, `list_length`, `encode_list`, and `encode_iter` functions'
  generics to be consistent with eachother and generic over `Borrow`
- Feature-gated `encode_fixed_size` to the `arrayvec` feature
- All `Decodable` implementations always advance the buffer, even when they
  return an error. This was not documented previously. Also applies to the
  implementations derived with the procedural macros.
- Improved `Header::decode` performance
- Documented `MaxEncodedLen` and `MaxEncodedLenAssoc`
- Improved general documentation

### Deprecated

- `DecodeError` in favor of just `Error` ([alloy-rs/core#182])

### Removed

- `derive` feature from defaults ([alloy-rs/core#159])

[alloy-rs/core#159]: https://github.com/alloy-rs/core/pull/159
[alloy-rs/core#182]: https://github.com/alloy-rs/core/pull/182

## [0.2.0] - 2023-06-23

### Changed

- Improve integer encoding performance ([alloy-rs/core#118])

[alloy-rs/core#118]: https://github.com/alloy-rs/core/pull/118

## [0.1.0] - 2023-06-13

### Added

- Initial release, forked from `reth_rlp` and `reth_rlp_derive`
