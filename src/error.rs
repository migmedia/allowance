use std::fmt::{Display, Formatter};
use std::num::{ParseFloatError, TryFromIntError};

#[derive(Debug, PartialEq)]
pub enum AllowanceError {
    ParseError(String),
    Overflow(String),
}

impl std::error::Error for AllowanceError {}

impl From<ParseFloatError> for AllowanceError {
    fn from(pfe: ParseFloatError) -> Self {
        AllowanceError::ParseError(match pfe.to_string().as_str() {
            "invalid float literal" => "invalid allowance literal".to_string(),
            "cannot parse float from empty string" => {
                "cannot parse allowance from empty string".to_string()
            }
            err => "Unknown error: ".to_string() + err,
        })
    }
}

impl From<TryFromIntError> for AllowanceError {
    fn from(t: TryFromIntError) -> Self {
        AllowanceError::Overflow(t.to_string())
    }
}

impl Display for AllowanceError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let text = match self {
            AllowanceError::ParseError(text) => text.as_str(),
            AllowanceError::Overflow(text) => text.as_str(),
        };
        write!(f, "{}", text)
    }
}
