use inlinable_string::{InlinableString, StringExt};

pub fn char_to_string(c: char) -> InlinableString {
    let mut s = InlinableString::new();
    s.push(c);
    s
}