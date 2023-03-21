use std::{env::args, error::Error, fmt::Display, fs, process::exit};

#[derive(Debug, Clone, PartialEq)]
enum BinOpKind {
    Add,
    Sub,
    Mul,
    Div,
}

impl BinOpKind {
    fn from_str(s: &str) -> Option<Self> {
        match s {
            "+" => Some(Self::Add),
            "-" => Some(Self::Sub),
            "*" => Some(Self::Mul),
            "/" => Some(Self::Div),
            _ => None,
        }
    }

    fn precedence(&self) -> u32 {
        match self {
            BinOpKind::Add | BinOpKind::Sub => 0,
            BinOpKind::Mul | BinOpKind::Div => 1,
        }
    }

    fn max_precedence() -> u32 {
        1
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Expr {
    Number(f64),
    Address {
        row: usize,
        col: usize,
    },
    BinOp {
        kind: BinOpKind,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self {
            Expr::Number(n) => write!(f, "{}", n)?,
            Expr::Address { row, col } => write!(
                f,
                "{col}{row}",
                col = (*col as u8 + 'A' as u8) as char,
                row = row + 1
            )?,
            Expr::BinOp { kind, lhs, rhs } => match kind {
                BinOpKind::Add => write!(f, "{lhs} + {rhs}")?,
                BinOpKind::Sub => write!(f, "{lhs} - {rhs}")?,
                BinOpKind::Mul => write!(f, "{lhs} * {rhs}")?,
                BinOpKind::Div => write!(f, "{lhs} / {rhs}")?,
            },
        }
        Ok(())
    }
}

struct Parser<'a>(&'a str);

impl<'a> Parser<'a> {
    fn peek(&mut self) -> Option<&'a str> {
        self.0 = &self.0.trim_start();
        let s = self.0;
        if s.is_empty() {
            return None;
        }
        if matches!(&s[..1], "+" | "-" | "*" | "/" | "(" | ")") {
            return Some(&s[..1]);
        }
        let n = s.chars().take_while(char::is_ascii_alphanumeric).count();
        if n > 0 {
            return Some(&s[..n]);
        } else {
            panic!("unknown token starting with: {}", s);
        }
    }

    fn next_token(&mut self) -> Option<&'a str> {
        let token = self.peek();
        if let Some(s) = token {
            self.0 = &self.0[s.len()..];
        }
        token
    }

    fn parse_primary_expr(&mut self) -> Expr {
        if let Some(token) = self.next_token() {
            if token == "(" {
                let expr = self.parse_expr();
                match self.next_token() {
                    Some(token) if token != ")" => {
                        panic!("Expectef `)` but got `{token}`");
                    }
                    None => panic!("Expected `)` but got end of input"),
                    _ => (),
                }
                return expr;
            }

            if let Ok(n) = token.parse() {
                return Expr::Number(n);
            }

            let col = match token.chars().nth(0) {
                Some(c) if c.is_ascii_alphabetic() => {
                    if c.is_ascii_uppercase() {
                        c as usize - 'A' as usize
                    } else {
                        c as usize - 'a' as usize
                    }
                }
                _ => panic!("Address must start with a letter: {token}"),
            };

            let row = match token[1..].parse::<usize>() {
                Ok(n) if n > 0 => n - 1,
                _ => panic!("Row must be an integer greater than one: {token}"),
            };

            return Expr::Address { row, col };
        }
        panic!("unexpected end of input");
    }

    fn parse_binop(&mut self, precedence: u32) -> Expr {
        if precedence > BinOpKind::max_precedence() {
            return self.parse_primary_expr();
        }
        let lhs = self.parse_binop(precedence + 1);

        match self.peek().map(BinOpKind::from_str).flatten() {
            Some(kind) if precedence == kind.precedence() => {
                self.next_token();
                let rhs = self.parse_binop(precedence);
                return Expr::BinOp {
                    kind,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                };
            }
            _ => return lhs,
        }
    }

    fn parse_expr(&mut self) -> Expr {
        self.parse_binop(0)
    }
}

impl<'a> Iterator for Parser<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_token()
    }
}

#[derive(Debug, Clone, PartialEq)]
enum CellKind {
    Text(String),
    Number(f64),
    Expr(Expr),
}

#[derive(Debug, PartialEq)]
struct Cell {
    kind: CellKind,
    evaluating: bool,
}

impl Cell {
    fn from(field: &str) -> Cell {
        let field = field.trim();
        if field.starts_with("=") {
            Cell {
                kind: CellKind::Expr(Parser(&field[1..]).parse_expr()),
                evaluating: false,
            }
        } else if let Ok(n) = field.parse() {
            Cell {
                kind: CellKind::Number(n),
                evaluating: false,
            }
        } else {
            Cell {
                kind: CellKind::Text(field.to_string()),
                evaluating: false,
            }
        }
    }
}

#[derive(Debug, PartialEq)]
enum EvalError {
    InvalidReference,
    Cycle,
}

impl Display for EvalError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EvalError::InvalidReference => write!(f, "invalid reference")?,
            EvalError::Cycle => write!(f, "cycle detected")?,
        }
        Ok(())
    }
}

impl Error for EvalError {}

#[derive(Debug, PartialEq)]
struct Sheet {
    rows: Vec<Vec<Cell>>,
}

impl Sheet {
    fn from_str(content: &str) -> Self {
        let mut rows = Vec::new();
        for line in content.lines() {
            let mut cells = Vec::new();
            for field in line.split("|") {
                cells.push(Cell::from(field));
            }
            rows.push(cells);
        }

        Sheet { rows }
    }

    fn eval_all(&mut self) -> Result<(), EvalError> {
        for i in 0..self.rows.len() {
            for j in 0..self.rows[i].len() {
                if let CellKind::Expr(_) = self.rows[i][j].kind {
                    self.eval_cell(i, j)?;
                }
            }
        }
        Ok(())
    }

    fn eval_cell(&mut self, i: usize, j: usize) -> Result<f64, EvalError> {
        if i >= self.rows.len() || j >= self.rows[i].len() {
            return Err(EvalError::InvalidReference);
        }

        if self.rows[i][j].evaluating {
            return Err(EvalError::Cycle);
        }

        match &self.rows[i][j].kind.clone() {
            CellKind::Expr(e) => {
                self.rows[i][j].evaluating = true;
                let n = self.eval_expr(e)?;
                self.rows[i][j].kind = CellKind::Number(n);
                self.rows[i][j].evaluating = false;
                Ok(n)
            }
            CellKind::Number(n) => Ok(*n),
            CellKind::Text(_) => Err(EvalError::InvalidReference),
        }
    }

    fn eval_expr(&mut self, expr: &Expr) -> Result<f64, EvalError> {
        match expr {
            Expr::Number(n) => Ok(*n),
            Expr::Address { row, col } => self.eval_cell(*row, *col),
            Expr::BinOp { kind, lhs, rhs } => {
                let lhs = self.eval_expr(lhs)?;
                let rhs = self.eval_expr(rhs)?;
                match kind {
                    BinOpKind::Add => Ok(lhs + rhs),
                    BinOpKind::Sub => Ok(lhs - rhs),
                    BinOpKind::Mul => Ok(lhs * rhs),
                    BinOpKind::Div => Ok(lhs / rhs),
                }
            }
        }
    }
}

impl Display for Sheet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for row in self.rows.iter() {
            for (col, cell) in row.iter().enumerate() {
                match &cell.kind {
                    CellKind::Expr(e) => write!(f, " = {e}")?,
                    CellKind::Number(n) => write!(f, " {n}")?,
                    CellKind::Text(t) => write!(f, " {t}")?,
                }
                if col != row.len() - 1 {
                    write!(f, " |")?;
                }
            }
            write!(f, "\n")?
        }
        Ok(())
    }
}

fn usage(program_name: &str) {
    eprintln!("usage: {program_name} input.csv > output.csv");
}
fn main() -> Result<(), Box<dyn Error>> {
    if let Some(file_name) = args().nth(1) {
        let content = fs::read_to_string(&file_name)?;
        let mut sheet = Sheet::from_str(&content);

        sheet.eval_all()?;

        println!("{sheet}");
    } else {
        usage(&args().nth(0).unwrap());
        exit(1);
    }

    // let input = "A1 + 69+B2 ";

    // println!("{input}");
    // let mut parser = Parser(input);

    // let expr = parser.parse_expr();

    // println!("{expr:#?}");

    Ok(())
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn cycle_detection() {
        let s = "\
            column 1 | column 2
            1        | 2
            3        | 4
            =B4+10   | =A3 + A4";
        let mut sheet = Sheet::from_str(s);
        assert_eq!(sheet.eval_all(), Err(EvalError::Cycle));
    }

    #[test]
    fn non_existing_cell() {
        let s = "\
            column 1 | column 2
            1        | 2
            3        | 4
            =B2+10   | =C10";
        let mut sheet = Sheet::from_str(s);
        assert_eq!(sheet.eval_all(), Err(EvalError::InvalidReference));
    }

    #[test]
    fn text_reference_in_expression() {
        let s = "\
            column 1 | column 2
            1        | 2
            3        | 4
            =B2+10   | =A1 + B1";
        let mut sheet = Sheet::from_str(s);
        assert_eq!(sheet.eval_all(), Err(EvalError::InvalidReference));
    }

    #[test]
    fn valid_sheet_plus() {
        let s1 = "\
            column 1 | column 2
            1        | 2
            3        | 4
            =B2+10   | =A2 + B2";
        let mut sheet1 = Sheet::from_str(s1);

        let s2 = "\
            column 1 | column 2
            1        | 2
            3        | 4
            12       | 3";
        let sheet2 = Sheet::from_str(s2);

        assert!(sheet1.eval_all().is_ok());
        assert_eq!(sheet1, sheet2);
    }

    #[test]
    fn valid_sheet_minus() {
        let s1 = "\
            column 1 | column 2
            1        | 2
            3        | 4
            =B2-10   | =A2 - B2";
        let mut sheet1 = Sheet::from_str(s1);

        let s2 = "\
            column 1 | column 2
            1        | 2
            3        | 4
            -8       | -1";
        let sheet2 = Sheet::from_str(s2);

        assert!(sheet1.eval_all().is_ok());
        assert_eq!(sheet1, sheet2);
    }

    #[test]
    fn parse_with_precedence1() {
        use BinOpKind::*;
        use Expr::*;
        let source = "2 * 3 + 1";

        let actual = Parser(&source).parse_expr();

        let expected = BinOp {
            kind: Add,
            lhs: Box::new(BinOp {
                kind: Mul,
                lhs: Box::new(Number(2.0)),
                rhs: Box::new(Number(3.0)),
            }),
            rhs: Box::new(Number(1.0)),
        };

        assert_eq!(actual, expected);
    }

    #[test]
    fn parse_with_precedence2() {
        use BinOpKind::*;
        use Expr::*;
        let source = "1 - 2 / 3";

        let actual = Parser(&source).parse_expr();

        let expected = BinOp {
            kind: Sub,
            lhs: Box::new(Number(1.0)),
            rhs: Box::new(BinOp {
                kind: Div,
                lhs: Box::new(Number(2.0)),
                rhs: Box::new(Number(3.0)),
            }),
        };

        assert_eq!(actual, expected);
    }

    #[test]
    fn parse_with_parentheses() {
        use BinOpKind::*;
        use Expr::*;
        let source = "(1 - 2) * 3";

        let actual = Parser(&source).parse_expr();

        let expected = BinOp {
            kind: Mul,
            lhs: Box::new(BinOp {
                kind: Sub,
                lhs: Box::new(Number(1.0)),
                rhs: Box::new(Number(2.0)),
            }),
            rhs: Box::new(Number(3.0)),
        };

        assert_eq!(actual, expected);
    }
}
