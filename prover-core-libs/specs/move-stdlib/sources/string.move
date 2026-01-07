module std::string_spec {
    use std::string;
    use std::string::String;
    use std::ascii;

    #[spec(prove)]
    fun utf8_spec(bytes: vector<u8>): String {
        let result = string::utf8(bytes);
        result
    }

    #[spec(prove)]
    fun from_ascii_spec(s: ascii::String): String {
        let result = string::from_ascii(s);
        result
    }

    #[spec(prove)]
    fun to_ascii_spec(s: String): ascii::String {
        let result = string::to_ascii(s);
        result
    }

    #[spec(prove)]
    fun try_utf8_spec(bytes: vector<u8>): Option<String> {
        let result = string::try_utf8(bytes);
        result
    }

    #[spec(prove)]
    fun as_bytes_spec(s: &String): &vector<u8> {
        let result = string::as_bytes(s);
        result
    }

    #[spec(prove)]
    fun into_bytes_spec(s: String): vector<u8> {
        let result = string::into_bytes(s);
        result
    }

    #[spec(prove)]
    fun is_empty_spec(s: &String): bool {
        let result = string::is_empty(s);
        result
    }

    #[spec(prove)]
    fun length_spec(s: &String): u64 {
        let result = string::length(s);
        result
    }

    #[spec(prove)]
    fun append_spec(s: &mut String, r: String) {
        string::append(s, r);
    }

    #[spec(prove)]
    fun append_utf8_spec(s: &mut String, bytes: vector<u8>) {
        string::append_utf8(s, bytes);
    }

    #[spec(prove)]
    fun insert_spec(s: &mut String, at: u64, o: String) {
        string::insert(s, at, o);
    }

    #[spec(prove)]
    fun substring_spec(s: &String, i: u64, j: u64): String {
        let result = string::substring(s, i, j);
        result
    }

    #[spec(prove)]
    fun index_of_spec(s: &String, r: &String): u64 {
        let result = string::index_of(s, r);
        result
    }

    #[spec(prove)]
    fun bytes_spec(s: &String): &vector<u8> {
        let result = string::bytes(s);
        result
    }

    #[spec(prove)]
    fun sub_string_spec(s: &String, i: u64, j: u64): String {
        let result = string::sub_string(s, i, j);
        result
    }
}
