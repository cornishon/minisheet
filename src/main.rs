use std::{env::args, error::Error, fmt::Display, fs, process::exit};

#[derive(Debug, Clone, PartialEq)]
enum BinOpKind {
    Plus,
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
                BinOpKind::Plus => write!(f, "{lhs} + {rhs}")?,
            },
        }
        Ok(())
    }
}

struct Parser<'a>(&'a str);

impl<'a> Parser<'a> {
    fn next_token(&mut self) -> Option<&'a str> {
        let s = self.0.trim_start();
        if s.is_empty() {
            return None;
        }
        if &s[..1] == "+" {
            self.0 = &s[1..];
            return Some(&s[..1]);
        }
        let n = s.chars().take_while(char::is_ascii_alphanumeric).count();
        if n > 0 {
            self.0 = &s[n..];
            return Some(&s[..n]);
        } else {
            panic!("unknown token starting with: {}", s);
        }
    }

    fn parse_primary_expr(&mut self) -> Expr {
        if let Some(token) = self.next_token() {
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

    fn parse_plus(&mut self) -> Expr {
        let lhs = self.parse_primary_expr();

        if let Some("+") = self.next_token() {
            let rhs = self.parse_plus();
            return Expr::BinOp {
                kind: BinOpKind::Plus,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            };
        } else {
            return lhs;
        }
    }

    fn parse_expr(&mut self) -> Expr {
        self.parse_plus()
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
            Expr::BinOp {
                kind: BinOpKind::Plus,
                lhs,
                rhs,
            } => Ok(self.eval_expr(lhs)? + self.eval_expr(rhs)?),
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
    fn valid_sheet() {
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
}
