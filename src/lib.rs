use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::fmt;

#[derive(Debug)]
pub enum JsonObject {
    Null,
    Boolean(bool),
    Integer(i64),
    Float(f64),
    String(String),
    Array(Vec<JsonObject>),
    Object(HashMap<String, JsonObject>),
}

impl PartialEq for JsonObject {
    fn eq(&self, rhs: &Self) -> bool {
        match (self, rhs) {
            (&JsonObject::Null, &JsonObject::Null) =>
                true,
            (&JsonObject::Boolean(l), &JsonObject::Boolean(r)) =>
                l == r,
            (&JsonObject::Integer(l), &JsonObject::Integer(r)) =>
                l == r,
            (&JsonObject::Float(l), &JsonObject::Float(r)) =>
                l == r,
            (&JsonObject::String(ref l), &JsonObject::String(ref r)) =>
                l == r,
            (&JsonObject::Array(ref l), &JsonObject::Array(ref r)) =>
                l == r,
            (&JsonObject::Object(ref l), &JsonObject::Object(ref r)) =>
                l == r,
            _ => false,
        }
    }
}

impl Eq for JsonObject {}

impl Hash for JsonObject {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            &JsonObject::Null =>
                (),
            &JsonObject::Boolean(n) =>
                n.hash(state),
            &JsonObject::Integer(n) =>
                n.hash(state),
            &JsonObject::Float(n) =>
                (n as i64).hash(state),
            &JsonObject::String(ref s) =>
                s.hash(state),
            &JsonObject::Array(ref a) =>
                a.hash(state),
            &JsonObject::Object(ref o) =>
                for (k, v) in o {
                    k.hash(state);
                    v.hash(state);
                },
        }
    }
}

impl fmt::Display for JsonObject {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &JsonObject::Null =>
                write!(f, "null"),
            &JsonObject::Boolean(n) =>
                write!(f, "{}", if n { "true" } else { "false" }),
            &JsonObject::Integer(n) =>
                write!(f, "{}", n),
            &JsonObject::Float(a) =>
                write!(f, "{}", a),
            &JsonObject::String(ref s) =>
                write!(f, "\"{}\"", s),
            &JsonObject::Array(ref arr) => {
                try!(write!(f, "["));
                let mut it = arr.iter();
                if let Some(e) = it.next() {
                    try!(write!(f, "{}", e));
                    while let Some(e) = it.next() {
                        try!(write!(f, ", {}", e));
                    }
                }
                write!(f, "]")
            },
            &JsonObject::Object(ref obj) => {
                try!(write!(f, "{{"));
                let mut it = obj.iter();
                if let Some((k, v)) = it.next() {
                    try!(write!(f, "\"{}\": {}", k, v));
                    while let Some((k, v)) = it.next() {
                        try!(write!(f, ", \"{}\": {}", k, v));
                    }
                }
                write!(f, "}}")
            },
        }
    }
}


#[derive(Debug)]
pub struct Error;

trait Parser {
    type Output;

    fn parse<'a>(&self, text: &'a str) -> Result<(Self::Output, &'a str), Error>;
}


struct OptionParser<P>(P);
impl<P: Parser> Parser for OptionParser<P> {
    type Output = Option<P::Output>;

    fn parse<'a>(&self, text: &'a str) -> Result<(Self::Output, &'a str), Error> {
        match self.0.parse(text) {
            Ok((r, text)) => Ok((Some(r), text)),
            Err(_) => Ok((None, text)),
        }
    }
}


struct Repeat0Parser<P>(P);
impl<P: Parser> Parser for Repeat0Parser<P> {
    type Output = Vec<P::Output>;

    fn parse<'a>(&self, text: &'a str) -> Result<(Self::Output, &'a str), Error> {
        let mut vec: Self::Output = Vec::new();
        match self.0.parse(text) {
            Ok((r, text)) => {
                vec.push(r);
                let mut rest = text;
                while let Ok((r, text)) = self.0.parse(rest) {
                    vec.push(r);
                    rest = text;
                }
                Ok((vec, rest))
            },
            Err(_) => Ok((vec, text))
        }
    }
}


struct Repeat1Parser<P>(P);
impl<P: Parser> Parser for Repeat1Parser<P> {
    type Output = Vec<P::Output>;

    fn parse<'a>(&self, text: &'a str) -> Result<(Self::Output, &'a str), Error> {
        match self.0.parse(text) {
            Ok((r, text)) => {
                let mut vec = vec![r];
                let mut rest = text;
                while let Ok((r, text)) = self.0.parse(rest) {
                    vec.push(r);
                    rest = text;
                }
                Ok((vec, rest))
            },
            Err(e) => Err(e),
        }
    }
}


struct Sequence2Parser<P1, P2>(P1, P2);
impl<P1: Parser, P2: Parser> Parser for Sequence2Parser<P1, P2> {
    type Output = (P1::Output, P2::Output);

    fn parse<'a>(&self, text: &'a str) -> Result<(Self::Output, &'a str), Error> {
        match self.0.parse(text) {
            Ok((r1, text)) => match self.1.parse(text) {
                Ok((r2, text)) => Ok(((r1, r2), text)),
                Err(e) => Err(e),
            },
            Err(e) => Err(e),
        }
    }
}


struct Sequence3Parser<P1, P2, P3>(P1, P2, P3);
impl<P1: Parser, P2: Parser, P3: Parser> Parser for Sequence3Parser<P1, P2, P3> {
    type Output = (P1::Output, P2::Output, P3::Output);

    fn parse<'a>(&self, text: &'a str) -> Result<(Self::Output, &'a str), Error> {
        match self.0.parse(text) {
            Ok((r1, text)) => match self.1.parse(text) {
                Ok((r2, text)) => match self.2.parse(text) {
                    Ok((r3, text)) => Ok(((r1, r2, r3), text)),
                    Err(e) => Err(e),
                },
                Err(e) => Err(e),
            },
            Err(e) => Err(e),
        }
    }
}


struct Sequence4Parser<P1, P2, P3, P4>(P1, P2, P3, P4);
impl<P1: Parser, P2: Parser, P3: Parser, P4: Parser> Parser for Sequence4Parser<P1, P2, P3, P4> {
    type Output = (P1::Output, P2::Output, P3::Output, P4::Output);

    fn parse<'a>(&self, text: &'a str) -> Result<(Self::Output, &'a str), Error> {
        match self.0.parse(text) {
            Ok((r1, text)) => match self.1.parse(text) {
                Ok((r2, text)) => match self.2.parse(text) {
                    Ok((r3, text)) => match self.3.parse(text) {
                        Ok((r4, text)) => Ok(((r1, r2, r3, r4), text)),
                        Err(e) => Err(e),
                    },
                    Err(e) => Err(e),
                },
                Err(e) => Err(e),
            },
            Err(e) => Err(e),
        }
    }
}


struct Choose2Parser<P1, P2>(P1, P2);
enum Choose2Param<P1, P2> { A(P1), B(P2), }
impl<P1: Parser, P2: Parser> Parser for Choose2Parser<P1, P2> {
    type Output = Choose2Param<P1::Output, P2::Output>;

    fn parse<'a>(&self, text: &'a str) -> Result<(Self::Output, &'a str), Error> {
        match self.0.parse(text) {
            Ok((r, text)) => Ok((Choose2Param::A(r), text)),
            _ => match self.1.parse(text) {
                Ok((r, text)) => Ok((Choose2Param::B(r), text)),
                Err(e) => Err(e),
            }
        }
    }
}


struct Choose7Parser<P1, P2, P3, P4, P5, P6, P7>(P1, P2, P3, P4, P5, P6, P7);
enum Choose7Param<P1, P2, P3, P4, P5, P6, P7> { A(P1), B(P2), C(P3), D(P4), E(P5), F(P6), G(P7), }
impl<P1: Parser, P2: Parser, P3: Parser, P4: Parser, P5: Parser, P6: Parser, P7: Parser> Parser for Choose7Parser<P1, P2, P3, P4, P5, P6, P7> {
    type Output = Choose7Param<P1::Output, P2::Output, P3::Output, P4::Output, P5::Output, P6::Output, P7::Output>;

    fn parse<'a>(&self, text: &'a str) -> Result<(Self::Output, &'a str), Error> {
        match self.0.parse(text) {
            Ok((r, text)) => Ok((Choose7Param::A(r), text)),
            _ => match self.1.parse(text) {
                Ok((r, text)) => Ok((Choose7Param::B(r), text)),
                _ => match self.2.parse(text) {
                    Ok((r, text)) => Ok((Choose7Param::C(r), text)),
                    _ => match self.3.parse(text) {
                        Ok((r, text)) => Ok((Choose7Param::D(r), text)),
                        _ => match self.4.parse(text) {
                            Ok((r, text)) => Ok((Choose7Param::E(r), text)),
                            _ => match self.5.parse(text) {
                                Ok((r, text)) => Ok((Choose7Param::F(r), text)),
                                _ => match self.6.parse(text) {
                                    Ok((r, text)) => Ok((Choose7Param::G(r), text)),
                                    Err(e) => Err(e),
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}


struct LiteralParser(&'static str);
impl Parser for LiteralParser {
    type Output = ();

    fn parse<'a>(&self, text: &'a str) -> Result<((), &'a str), Error> {
        if text.len() < self.0.len() {
            return Err(Error)
        } else {
            let mut it = text.chars();
            for k in self.0.chars() {
                if let Some(ch) = it.next() {
                    if ch != k {
                        return Err(Error)
                    }
                }
            }
            return Ok(((), it.as_str()))
        }
    }
}


struct SpaceParser;
impl Parser for SpaceParser {
    type Output = ();

    fn parse<'a>(&self, text: &'a str) -> Result<((), &'a str), Error> {
        let mut it = text.chars();
        let mut rest = it.as_str();
        if let Some(ch) = it.next() {
            if ch.is_whitespace() {
                rest = it.as_str();
            }
        }
        Ok(((), rest))
    }
}


struct CharParser(&'static str);
impl Parser for CharParser {
    type Output = char;

    fn parse<'a>(&self, text: &'a str) -> Result<(char, &'a str), Error> {
        let mut it = text.chars();
        if let Some(ch) = it.next() {
            for k in self.0.chars() {
                if ch == k {
                    return Ok((ch, it.as_str()))
                }
            }
        }
        return Err(Error)
    }
}


struct DigitsParser;
impl Parser for DigitsParser {
    type Output = i32;

    fn parse<'a>(&self, text: &'a str) -> Result<(i32, &'a str), Error> {
        match Repeat1Parser(CharParser("0123456789")).parse(text) {
            Ok((vec, text)) => {
                let mut num: i32 = 0;
                for ch in vec {
                    num = num * 10 + (ch  as i32 - '0' as i32);
                }
                Ok((num, text))
            },
            Err(e) => Err(e),
        }
    }
}


struct BooleanParser;
impl Parser for BooleanParser {
    type Output = bool;

    fn parse<'a>(&self, text: &'a str) -> Result<(bool, &'a str), Error> {
        match Choose2Parser(
            LiteralParser("true"), LiteralParser("false")
        ).parse(text) {
            Ok((Choose2Param::A(_), text)) => Ok((true, text)),
            Ok((Choose2Param::B(_), text)) => Ok((false, text)),
            _ => Err(Error),
        }
    }
}

struct IntegerParser;
impl Parser for IntegerParser {
    type Output = i64;

    fn parse<'a>(&self, text: &'a str) -> Result<(i64, &'a str), Error> {
        match Sequence2Parser(
            OptionParser(CharParser("+-")),
            DigitsParser
        ).parse(text) {
            Ok(((sign, dec), text)) => Ok((if let Some('-') = sign { -dec } else { dec } as i64, text)),
            _ => Err(Error),
        }
    }
}


struct FloatParser;
impl Parser for FloatParser {
    type Output = f64;

    fn parse<'a>(&self, text: &'a str) -> Result<(f64, &'a str), Error> {
        match Sequence4Parser(
            IntegerParser,
            LiteralParser("."),
            OptionParser(DigitsParser),
            OptionParser(Sequence2Parser(CharParser("eE"), IntegerParser)),
        ).parse(text) {
            Ok(((dec, _, frac, eps), text)) => {
                let mut num = dec as f64;
                if let Some(frac) = frac {
                    let frac = (frac as f64) / (10 as f64).powi(1 + ((frac as f64).log10()) as i32);
                    num += if num >= 0. { frac } else { -frac };
                }
                if let Some((_, eps)) = eps {
                    let eps = (10 as f64).powi(eps as i32);
                    num *= eps;
                }
                Ok((num, text))
            }
            _ => Err(Error),
        }
    }
}


struct StringSymbolParser;
impl Parser for StringSymbolParser {
    type Output = char;

    fn parse<'a>(&self, text: &'a str) -> Result<(char, &'a str), Error> {
        let mut it = text.chars();
        match it.next() {
            Some('"') => Err(Error),
            Some('\\') => {
                let ch = match it.next() {
                    Some('"') => '"',
                    Some('\\') =>'\\',
                    Some('/') => '/',
                    Some('b') => 0x08 as char,
                    Some('f') => 0x0C as char,
                    Some('n') => '\n',
                    Some('r') => '\r',
                    Some('t') => '\t',
                    Some('u') => {
                        let mut hex: u16 = 0;
                        for _ in 0..4 {
                            if let Some(ch) = it.next() {
                                if '0' <= ch && ch <= '9' {
                                    hex = hex * 16 + (ch as u16 - '0' as u16);
                                } else if 'a' <= ch && ch <= 'f' {
                                    hex = hex * 16 + (ch as u16 - 'a' as u16) + 10;
                                } else if 'A' <= ch && ch <= 'F' {
                                    hex = hex * 16 + (ch as u16 - 'A' as u16) + 10;
                                } else {
                                    return Err(Error)
                                }
                            } else {
                                return Err(Error)
                            }
                        }
                        '!'  // TODO: utf16 to char
                    },
                    _ => return Err(Error),
                };
                Ok((ch, it.as_str()))
            },
            Some(c) if c.is_alphanumeric() => Ok(((c), it.as_str())),
            _ => Err(Error),
        }
    }
}


struct StringParser;
impl Parser for StringParser {
    type Output = String;

    fn parse<'a>(&self, text: &'a str) -> Result<(String, &'a str), Error> {
        match Sequence3Parser(
            LiteralParser("\""),
            Repeat0Parser(StringSymbolParser),
            LiteralParser("\"")
        ).parse(text) {
            Ok(((_, vec, _), text)) => {
                let mut s = String::new();
                for ch in vec {
                    s.push(ch);
                }
                Ok((s, text))
            }
            _ => Err(Error),
        }
    }
}


// array := '[' (Json (',' Json)* )? ']'
struct ArrayParser;
impl Parser for ArrayParser {
    type Output = Vec<JsonObject>;

    fn parse<'a>(&self, text: &'a str) -> Result<(Vec<JsonObject>, &'a str), Error> {
        let beg = Sequence2Parser(LiteralParser("["), SpaceParser);
        let sep = Sequence3Parser(SpaceParser, LiteralParser(","), SpaceParser);
        let end = Sequence2Parser(SpaceParser, LiteralParser("]"));

        match Sequence3Parser(
            beg,
            OptionParser(
                Sequence2Parser(
                    JsonParser,
                    Repeat0Parser(
                        Sequence2Parser(sep, JsonParser)
                    )
                )
            ),
            end
        ).parse(text) {
            Ok(((_, opt, _), text)) => {
                let mut arr = Vec::new();
                if let Some((e, tail)) = opt {
                    arr.push(e);
                    for (_, e) in tail {
                        arr.push(e);
                    }
                }
                Ok((arr, text))
            },
            _ => Err(Error),
        }
    }
}


// object = '{' (Str ':' Json (',' Str ':' Json)* )? '}'
struct ObjectParser;
impl Parser for ObjectParser {
    type Output = HashMap<String, JsonObject>;

    fn parse<'a>(&self, text: &'a str) -> Result<(HashMap<String, JsonObject>, &'a str), Error> {
        let beg = Sequence2Parser(LiteralParser("{"), SpaceParser);
        let sep = Sequence3Parser(SpaceParser, LiteralParser(","), SpaceParser);
        let re1 = Sequence3Parser(SpaceParser, LiteralParser(":"), SpaceParser);
        let re2 = Sequence3Parser(SpaceParser, LiteralParser(":"), SpaceParser);
        let end = Sequence2Parser(SpaceParser, LiteralParser("}"));

        match Sequence3Parser(
            beg,
            OptionParser(
                Sequence4Parser(
                    StringParser,
                    re1,
                    JsonParser,
                    Repeat0Parser(
                        Sequence4Parser(
                            sep,
                            StringParser,
                            re2,
                            JsonParser
                        )
                    )
                )
            ),
            end
        ).parse(text) {
            Ok(((_, opt, _), text)) => {
                let mut obj = HashMap::new();
                if let Some((k, _, v, tail)) = opt {
                    obj.insert(k, v);
                    for (_, k, _, v) in tail {
                        obj.insert(k, v);
                    }
                }
                Ok((obj, text))
            },
            _ => Err(Error),
        }
    }
}


struct JsonParser;
impl Parser for JsonParser {
    type Output = JsonObject;

    fn parse<'a>(&self, text: &'a str) -> Result<(JsonObject, &'a str), Error> {
        match Choose7Parser(
            LiteralParser("null"),
            BooleanParser,
            ObjectParser,
            ArrayParser,
            StringParser,
            FloatParser,
            IntegerParser
        ).parse(text) {
            Ok((Choose7Param::A(_), text)) => Ok((JsonObject::Null, text)),
            Ok((Choose7Param::B(b), text)) => Ok((JsonObject::Boolean(b), text)),
            Ok((Choose7Param::C(o), text)) => Ok((JsonObject::Object(o), text)),
            Ok((Choose7Param::D(a), text)) => Ok((JsonObject::Array(a), text)),
            Ok((Choose7Param::E(s), text)) => Ok((JsonObject::String(s), text)),
            Ok((Choose7Param::F(f), text)) => Ok((JsonObject::Float(f), text)),
            Ok((Choose7Param::G(i), text)) => Ok((JsonObject::Integer(i), text)),
            _ => Err(Error),
        }
    }
}


pub fn parse(text: &str) -> Result<JsonObject, Error> {
    match JsonParser.parse(text) {
        Ok((json, _)) => Ok(json),
        Err(e) => Err(e),
    }
}


#[test]
fn test_literal_parser() {
    assert!(LiteralParser("hoge").parse("hoge").unwrap() == ((), ""));
    assert!(LiteralParser("hoge").parse("hogefuga").unwrap() == ((), "fuga"));
    assert!(LiteralParser("fuga").parse("hoge").is_err());
}


#[test]
fn test_char_parser() {
    assert!(CharParser("+-").parse("+100").unwrap() == (('+', "100")));
    assert!(CharParser("0").parse("+100").is_err());
}

#[test]
fn test_option_parser() {
    assert!(OptionParser(CharParser("+-")).parse("+100").unwrap() == (Some('+'), "100"));
    assert!(OptionParser(CharParser("+-")).parse("100").unwrap() == (None, "100"));
}

#[test]
fn test_repeat_parser() {
    assert!(Repeat1Parser(CharParser("0123456789")).parse("100").unwrap() == (vec!['1', '0', '0'], ""));
}

#[test]
fn test_digits_parser() {
    assert!(DigitsParser.parse("100").unwrap() == (100, ""));
}

#[test]
fn test_integer_parser() {
    assert!(IntegerParser.parse("1").unwrap() == (1, ""));
    assert!(IntegerParser.parse("100 ").unwrap() == (100, " "));
    assert!(IntegerParser.parse("9999.").unwrap() == (9999, "."));
    assert!(IntegerParser.parse("+100").unwrap() == (100, ""));
    assert!(IntegerParser.parse("-012").unwrap() == (-12, ""));
}

#[test]
fn test_float_parser() {
    assert!(FloatParser.parse("100.").unwrap() == (100., ""));
    assert!(FloatParser.parse("123.456").unwrap() == (123.456, ""));
    assert!(FloatParser.parse("-987.654").unwrap() == (-987.654, ""));
    assert!(FloatParser.parse("14.14e1").unwrap() == (141.4, ""));
    assert!(FloatParser.parse("3.E-2").unwrap() == (0.03, ""));
    assert!(FloatParser.parse("+14.14e+1").unwrap() == (141.4, ""));
    assert!(FloatParser.parse("-3.E-2").unwrap() == (-0.03, ""));
}

#[test]
fn test_string_parser() {
    assert!(StringParser.parse("\"hello\"").unwrap() == ("hello".to_string(), ""));
}

#[test]
fn test_array_parser() {
    assert!(ArrayParser.parse("[]").unwrap() == (vec![], ""));
    assert!(ArrayParser.parse("[ ]").unwrap() == (vec![], ""));
    assert!(ArrayParser.parse("[ 10,20. ]").unwrap() == (vec![
        JsonObject::Integer(10),
        JsonObject::Float(20.)
    ], ""));
    assert!(ArrayParser.parse("[ 10 , \"hello\", true ,null]").unwrap() == (vec![
        JsonObject::Integer(10),
        JsonObject::String("hello".to_string()),
        JsonObject::Boolean(true),
        JsonObject::Null
    ], ""));
}

#[test]
fn test_object_parser() {
    assert!(ObjectParser.parse("{\"hello\": \"world\"}").unwrap() == ({
        let mut map: HashMap<String, JsonObject> = HashMap::new();
        map.insert("hello".to_string(), JsonObject::String("world".to_string()));
        map
    }, ""));

    assert!(ObjectParser.parse("{\"hello\": \"world\",\"hoge\": false }").unwrap() == ({
        let mut map: HashMap<String, JsonObject> = HashMap::new();
        map.insert("hello".to_string(), JsonObject::String("world".to_string()));
        map.insert("hoge".to_string(), JsonObject::Boolean(false));
        map
    }, ""));

    assert!(ObjectParser.parse("{\"hello\": \"world\",\"hoge\": false , \"fuga\" : 100}").unwrap() == ({
        let mut map: HashMap<String, JsonObject> = HashMap::new();
        map.insert("hello".to_string(), JsonObject::String("world".to_string()));
        map.insert("hoge".to_string(), JsonObject::Boolean(false));
        map.insert("fuga".to_string(), JsonObject::Integer(100));
        map
    }, ""));

    assert!(ObjectParser.parse("{\"hello\": \"world\",\"hoge\": false, \"array\": [1,2,3,4,5] }").unwrap() == ({
        let mut map: HashMap<String, JsonObject> = HashMap::new();
        map.insert("hello".to_string(), JsonObject::String("world".to_string()));
        map.insert("hoge".to_string(), JsonObject::Boolean(false));
        map.insert("array".to_string(), JsonObject::Array(vec![
            JsonObject::Integer(1),
            JsonObject::Integer(2),
            JsonObject::Integer(3),
            JsonObject::Integer(4),
            JsonObject::Integer(5)
        ]));
        map
    }, ""));
}
