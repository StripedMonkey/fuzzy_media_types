A work in progress Media-Type parsing library

Allows for relatively easy interpreting of Content-Type headers and "fuzzy" matching of subtypes

```rust
use fuzzy_mime::BorrowedMediaType;
let media_type = BorrowedMediaType::parse("application/json;charset=utf-8").unwrap();
assert!(media_type.matches("application/json"))
```