#![deny(missing_docs)]
//! Simple Media-Type library that focuses on ease of use
//! Media Types are
//! > used to specify the media type and subtype of data in the body of a message and to
//! fully specify the native representation (canonical form) of such data
//! --
//! Based on [RFC-7231](https://www.rfc-editor.org/rfc/rfc7231) and [RFC-2046](https://www.rfc-editor.org/rfc/rfc2046)
//! and originally developed from [RFC-1049](https://www.rfc-editor.org/rfc/rfc1049)
use std::{
    collections::{hash_map::Iter, HashMap},
    fmt::{Debug, Display},
};

// TODO: Stop conflating Content-Type and Media-Type

/// A borrowed Media-Type
/// The main type everything is implemented for
///
/// Media types specify the contents of a message or body, but can be more specific than your code requires
/// Any media type that is *less specific* should match.
/// ```
/// use fuzzy_mime::BorrowedMediaType;
/// let media_type = BorrowedMediaType::parse("application/json;charset=utf-8").unwrap();
/// assert!(media_type.matches("application/json"))
/// ```
/// Mime types which are more specific will *fail*
/// ```should_panic
/// use fuzzy_mime::BorrowedMediaType;
/// let media_type = BorrowedMediaType::parse("application/json").unwrap();
/// assert!(media_type.matches("application/json;charset=utf-8"))
/// ```
///
/// Structured types that extend another also work
/// ```
/// use fuzzy_mime::BorrowedMediaType;
/// let media_type = BorrowedMediaType::parse("application/vnd.docker.distribution.manifest.v1+json").unwrap();
/// assert!(media_type.matches("application/json"))
/// ```
#[derive(Debug)]
pub struct BorrowedMediaType<'a> {
    primary_type: &'a str,
    sub_type: &'a str, // Is the sub type necessary with a structured/unstructured component?
    structured: &'a str,
    unstructured: &'a str, // TODO: Name this better
    parameters: HashMap<String, &'a str>,
}

/// Possible errors when parsing a Media-Type
#[derive(Debug)]
pub enum ParseError {
    /// Generic invalid Media-Type
    InvalidMediaType,
    /// Invalid Content-Type style parameters detected
    InvalidParameter,
}

impl<'a> BorrowedMediaType<'a> {
    /// Try to parse a Content-Type string
    /// Will return [`ParseError`]
    pub fn parse(content_type_str: &str) -> Result<BorrowedMediaType, ParseError> {
        // There's no possbile way this could be incorrect
        let structured;
        let unstructured;
        if let Some((primary_type, rest)) = content_type_str.split_once('/') {
            if let Some((sub_type, rest)) = rest.split_once(';') {
                if let Some(type_parts) = sub_type.rsplit_once('+') {
                    (unstructured, structured) = type_parts
                } else {
                    // There's surely a better way to handle there not being a structured component
                    (unstructured, structured) = (sub_type, sub_type)
                }
                // "Unlike some similar constructs in other header fields, media type
                // parameters do not allow whitespace (even "bad" whitespace) around
                // the "=" character."
                let mut parameters = HashMap::new();
                for kv in rest.split(';') {
                    let kv = kv.trim();
                    if let Some((key, maybe_quoted)) = kv.split_once('=') {
                        parameters.insert(
                            key.to_string().to_ascii_lowercase(),
                            maybe_quoted.trim_matches('"'),
                        );
                    } else {
                        return Err(ParseError::InvalidParameter); // Empty parameters?
                    }
                }
                Ok(BorrowedMediaType {
                    primary_type,
                    sub_type,
                    structured,
                    unstructured,
                    parameters,
                })
            } else {
                if let Some(type_parts) = rest.rsplit_once('+') {
                    (unstructured, structured) = type_parts
                } else {
                    (unstructured, structured) = (rest, rest)
                }
                Ok(BorrowedMediaType {
                    primary_type,
                    sub_type: rest,
                    structured,
                    unstructured,
                    parameters: HashMap::new(),
                })
            }
        } else {
            Err(ParseError::InvalidMediaType) // No Subtype?
        }
    }

    /// Determines whether `self` is a subtype of `content_type`
    pub fn matches<T>(&self, content_type: T) -> bool
    where
        T: TryInto<BorrowedMediaType<'a>>,
        <T as TryInto<BorrowedMediaType<'a>>>::Error: Debug, // TODO: This is ugly.
    {
        let content_match = content_type.try_into().unwrap();

        self.matches_type(&content_match)
            && self.matches_subtype(&content_match)
            && self.matches_params(&content_match)
    }

    fn matches_type(&self, content_match: &BorrowedMediaType) -> bool {
        self.primary_type
            .eq_ignore_ascii_case(content_match.primary_type)
    }

    fn matches_subtype(&self, content_match: &BorrowedMediaType) -> bool {
        self.sub_type.eq_ignore_ascii_case(content_match.sub_type)
            || self.structured.eq_ignore_ascii_case(content_match.sub_type)
            || self
                .unstructured
                .eq_ignore_ascii_case(content_match.structured)
    }

    fn matches_params(&self, content_match: &BorrowedMediaType) -> bool {
        for (key, value) in content_match.get_params() {
            match self.parameters.get(key) {
                Some(self_value) => {
                    if !self_value.eq_ignore_ascii_case(value) {
                        return false;
                    }
                }
                None => return false,
            }
        }
        true
    }

    /// Returns an unordered iterator over all parameters
    pub fn get_params(&self) -> Iter<String, &str> {
        self.parameters.iter()
    }

    /// Checks whether a media type has any parameters
    pub fn has_params(&self) -> bool {
        !self.parameters.is_empty()
    }
}

impl<'a> TryFrom<&'a str> for BorrowedMediaType<'a> {
    type Error = ParseError;

    fn try_from(value: &'a str) -> Result<Self, Self::Error> {
        BorrowedMediaType::parse(value)
    }
}

impl<'a> From<&BorrowedMediaType<'a>> for BorrowedMediaType<'a> {
    fn from(t: &BorrowedMediaType<'a>) -> Self {
        BorrowedMediaType {
            primary_type: t.primary_type,
            sub_type: t.sub_type,
            structured: t.structured,
            unstructured: t.unstructured,
            parameters: t.parameters.clone(),
        }
    }
}

impl<'a> Display for BorrowedMediaType<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{primary}/{sub}",
            primary = self.primary_type,
            sub = self.sub_type
        )?;
        for (key, value) in &self.parameters {
            write!(f, ";{key}={value}")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let content_type = "application/json; charset=utf-8";
        let c = BorrowedMediaType::parse(content_type).unwrap();
        assert_eq!(c.primary_type, "application");
        assert_eq!(c.sub_type, "json");
        assert_eq!(c.parameters["charset"], "utf-8");
    }

    #[test]
    fn match_different_ascii_case_types() {
        /*
         * A parameter value that matches the token production can be
         * transmitted either as a token or within a quoted-string.  The quoted
         * and unquoted values are equivalent.  For example, the following
         * examples are all equivalent, but the first is preferred for
         * consistency:
         *
         *   text/html;charset=utf-8
         *   text/html;charset=UTF-8
         *   Text/HTML;Charset="utf-8"
         *   text/html; charset="utf-8"
         */
        let html_text_cases = vec![
            r#"text/html;charset=utf-8"#,
            r#"text/html;charset=UTF-8"#,
            r#"Text/HTML;Charset="utf-8""#,
            r#"text/html; charset="utf-8""#,
        ];
        let mut html_text_types = Vec::new();
        for case in html_text_cases {
            let test_case = BorrowedMediaType::parse(case).expect("Failed to parse test case");
            html_text_types.push(test_case);
        }
        // Combanatorial stuffs
        println!("Testing borrowed content types against each other");
        for content_type_a in &html_text_types {
            for content_type_b in &html_text_types {
                assert!(
                    content_type_a.matches(content_type_b),
                    "Content {content_type_a} does not match {content_type_b}"
                );
            }
        }
    }

    #[test]
    fn dont_match_differing_types() {
        let type_strings = vec!["text/plain", "text/html", "application/json"];

        let types: HashMap<&str, BorrowedMediaType> = type_strings
            .iter()
            .map(|s| (*s, BorrowedMediaType::parse(s).unwrap()))
            .collect();

        for (type_string_a, type_struct_a) in types.iter() {
            for (type_string_b, type_struct_b) in types.iter() {
                if type_string_a != type_string_b {
                    assert!(
                        !type_struct_a.matches(type_struct_b),
                        "{type_string_a} matches {type_string_b} when it shouldn't!"
                    )
                }
            }
        }
    }

    #[test]
    fn dont_match_differing_parameters() {
        let type_strings = vec![
            r#"text/html;charset=iso-ir-15"#,
            r#"text/html;charset=utf-8"#,
            r#"text/html;charset=Cyrillic-Asian"#,
        ];

        let types: HashMap<&str, BorrowedMediaType> = type_strings
            .iter()
            .map(|s| (*s, BorrowedMediaType::parse(s).unwrap()))
            .collect();

        for (type_string_a, type_struct_a) in types.iter() {
            for (type_string_b, type_struct_b) in types.iter() {
                if type_string_a != type_string_b {
                    assert!(
                        !type_struct_a.matches(type_struct_b),
                        "{type_string_a} matches {type_string_b} when it shouldn't!"
                    )
                }
            }
        }
    }

    #[test]
    fn match_subsets() {
        /*
         * Matching subsets is something of a problem in that the rules around subsets
         * are convoluted. For instance, some charsets are subsets of each other. Any
         * valid ASCII is valid utf-8.
         *
         * My current solution is to have a "literal" match only for the time being
         */
        let should_match = vec![
            ("text/json;charset=utf-8", "text/json"),
            ("application/json;charset=utf-8", "application/json"),
        ];
        for set in should_match.iter().map(|x| {
            (
                BorrowedMediaType::parse(x.0).unwrap(),
                BorrowedMediaType::parse(x.1).unwrap(),
            )
        }) {
            assert!(
                set.0.matches(&set.1),
                "{} didn't match with {} when it should!",
                set.0,
                set.1
            )
        }
        let shouldnt_match = vec![
            ("text/json", "text/json;charset=utf-8"),
            ("application/json", "application/json;charset=utf-8"),
        ];
        assert_matches(shouldnt_match, |a, b| {
            assert!(!a.matches(b), "{} matched with {} when it shouldn't!", a, b);
        });
    }

    #[test]
    fn match_structured() {
        let should_match = vec![
            (
                "application/vnd.docker.distribution.manifest.v1+json",
                "application/json",
            ),
            (
                "application/vnd.docker.distribution.manifest.v2+json",
                "application/json",
            ),
            ("application/aif+cbor", "application/aif"),
        ];
        assert_matches(should_match, |a, b| {
            assert!(
                a.matches(b),
                "{} didn't match with {} when it should!",
                a,
                b
            )
        });
    }

    #[test]
    fn dont_match_structured() {
        let shouldnt_match = vec![
            ("application/aif+cbor", "application/aif+json"),
            ("application/elm+json", "application/elm+xml"),
            (
                // Because you don't know if it's xml or anything else. B is not a subset of A
                "application/elm",
                "application/elm+xml",
            ),
        ];
        assert_matches(shouldnt_match, |a, b| {
            assert!(!a.matches(b), "{} matched with {} when it shouldn't!", a, b);
        });
    }

    #[test]
    #[ignore]
    fn match_fuzzy() {
        /*
         * This is what I'd like to eventually be able to check
         * A must be a superset of B. For instance since UTF-8
         * is a superset of ASCII this should be allowed.
         * Essentially any type which can be reasonably
         * interpreted by as another type should be allowed.
         *
         * Additionally there are a few types which *can* appear
         * even though they shouldn't. I.E `text/json` despite
         * the fact it should be `application/json`
         */
        let should_match = vec![
            ("text/json;charset=utf-8", "text/json;charset=ascii"),
            ("application/json;charset=utf-8", "text/plain"),
            ("text/json", "application/json"),
            ("application/json", "text/json"),
            (
                "application/vnd.docker.distribution.manifest.v1+json",
                "application/json",
            ),
        ];
        assert_matches(should_match, |a, b| {
            assert!(
                a.matches(b),
                "{} didn't match with {} when it should!",
                a,
                b
            )
        });
    }

    fn assert_matches<F>(should_match: Vec<(&str, &str)>, assertion: F)
    where
        F: Fn(&BorrowedMediaType, &BorrowedMediaType),
    {
        for (a, b) in should_match.iter().map(|x| {
            (
                BorrowedMediaType::parse(x.0).unwrap(),
                BorrowedMediaType::parse(x.1).unwrap(),
            )
        }) {
            assertion(&a, &b)
        }
    }
}
