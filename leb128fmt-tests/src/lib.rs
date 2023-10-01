#[cfg(test)]
mod tests {
    use leb128fmt::*;

    use proptest::prelude::*;

    proptest! {
        #[allow(clippy::ignored_unit_patterns)]
        #[test]
        fn test_encode_decode_u32_num(n in any::<u32>()) {
            let (bytes, written_len) = encode_u32(n).unwrap();
            let (decoded_n, read_len) = decode_u32(bytes).unwrap();
            prop_assert_eq!(decoded_n, n);
            prop_assert_eq!(written_len, read_len);
        }

        #[allow(clippy::ignored_unit_patterns)]
        #[test]
        fn test_encode_fixed_decode_u32_num(n in any::<u32>()) {
            let bytes = encode_fixed_u32(n).unwrap();
            let (decoded_n, read_len) = decode_u32(bytes).unwrap();
            prop_assert_eq!(decoded_n, n);
            prop_assert_eq!(bytes.len(), read_len);
        }

        #[allow(clippy::ignored_unit_patterns)]
        #[test]
        fn test_encode_decode_u64_num(n in any::<u64>()) {
            let (bytes, written_len) = encode_u64(n).unwrap();
            let (decoded_n, read_len) = decode_u64(bytes).unwrap();
            prop_assert_eq!(decoded_n, n);
            prop_assert_eq!(written_len, read_len);
        }

        #[allow(clippy::ignored_unit_patterns)]
        #[test]
        fn test_encode_fixed_decode_u64_num(n in any::<u64>()) {
            let bytes = encode_fixed_u64(n).unwrap();
            let (decoded_n, read_len) = decode_u64(bytes).unwrap();
            prop_assert_eq!(decoded_n, n);
            prop_assert_eq!(bytes.len(), read_len);
        }

        #[allow(clippy::ignored_unit_patterns)]
        #[test]
        fn test_decode_u32_bytes(bytes in prop::array::uniform5(any::<u8>())) {
             if decode_u32(bytes).is_none() {
                for b in bytes.iter().take(4) {
                    prop_assert!(b & 0x80 != 0);
                }
                prop_assert!(bytes[4] > 0x0f);
                return Ok(());
            }
        }

        #[allow(clippy::ignored_unit_patterns)]
        #[test]
        fn test_decode_u64_bytes(bytes in prop::array::uniform10(any::<u8>())) {
            if decode_u64(bytes).is_none() {
                for b in bytes.iter().take(9) {
                    prop_assert!(b & 0x80 != 0);
                }
                prop_assert!(bytes[9] > 0x01);
                return Ok(());
            }
        }
    }
}
