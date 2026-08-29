use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn new(start: u32, end: u32) -> Self {
        Self { start, end }
    }

    pub fn dummy() -> Self {
        Self { start: 0, end: 0 }
    }
}

/// `#[serde(with = "span_keyed_map")]` for a `HashMap<Span, V>`, which JSON
/// otherwise rejects — it only allows string map keys, and `Span` is a struct.
/// Round-trips as a sequence of `[span, value]` pairs instead.
pub mod span_keyed_map {
    use super::Span;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use std::collections::HashMap;

    pub fn serialize<V, S>(map: &HashMap<Span, V>, s: S) -> Result<S::Ok, S::Error>
    where
        V: Serialize,
        S: Serializer,
    {
        map.iter().collect::<Vec<_>>().serialize(s)
    }

    pub fn deserialize<'de, V, D>(d: D) -> Result<HashMap<Span, V>, D::Error>
    where
        V: Deserialize<'de>,
        D: Deserializer<'de>,
    {
        Ok(Vec::<(Span, V)>::deserialize(d)?.into_iter().collect())
    }
}

/// `#[serde(with = "float32_bits")]` for an `f32` field that can hold
/// `nan32`/`infinity32` — plain `serde_json` serializes non-finite floats as
/// JSON `null` (JSON's number grammar has no NaN/Infinity), which then fails
/// to deserialize back into an `f32` at all ("invalid type: null, expected
/// f32"). Every `Cantor` `ExprKind::FloatLit`/`SemExprKind::FloatLit` value
/// crosses `solver::worker`'s subprocess boundary as JSON, so this round-
/// trips via the raw IEEE bit pattern instead — lossless for every value,
/// finite or not.
pub mod float32_bits {
    use serde::{Deserialize, Deserializer, Serializer};

    pub fn serialize<S>(x: &f32, s: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        s.serialize_u32(x.to_bits())
    }

    pub fn deserialize<'de, D>(d: D) -> Result<f32, D::Error>
    where
        D: Deserializer<'de>,
    {
        Ok(f32::from_bits(u32::deserialize(d)?))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Symbol(pub String);

impl Symbol {
    pub fn new(name: impl Into<String>) -> Self {
        Self(name.into())
    }
}

impl std::fmt::Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// Convert a byte offset into a source string to a 1-based (line, column) pair.
///
/// Both `line` and `col` count from 1. Columns count Unicode scalar values,
/// not bytes, so multi-byte characters count as one column.
pub fn offset_to_line_col(src: &str, offset: u32) -> (u32, u32) {
    let offset = (offset as usize).min(src.len());
    let prefix = &src[..offset];
    let line = prefix.bytes().filter(|&b| b == b'\n').count() as u32 + 1;
    let col_start = prefix.rfind('\n').map(|i| i + 1).unwrap_or(0);
    let col = prefix[col_start..].chars().count() as u32 + 1;
    (line, col)
}
