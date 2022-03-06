use std::cmp::Ordering;
use std::convert::TryFrom;
use std::fmt::{Debug, Display, Formatter};
use std::num::ParseFloatError;
use std::ops::{Add, AddAssign, Deref, Div, Mul, Neg, Sub, SubAssign};

///
/// # Measure
///
/// A type to calculate lossless dimensions with a fixed precision.
/// All sizes are defined in the tenth fraction of `μ`:
///
///  * 10 = 1 μ
///  * 10_000  = 1 mm
///  * 10_000_000  = 1 m
///
/// The standard `Display::fmt`-methode represents the value in `mm`. The *alternate* Display
/// shows the `i64` value.
///
/// As 10_000 = 1 mm  
///
/// ### Example:
/// ```rust
///#     use allowance::Measure;
///     let measure = Measure::from(12.5);
///
///     assert_eq!(format!("{measure}"),"12.5000");
///     assert_eq!(format!("{measure:.2}"), "12.50");
///     assert_eq!(format!("{measure:#}"), "125000");
/// ```
///
///

#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Measure(i64);

pub enum Unit {
    /// my-meter `μ`
    MY,
    /// millimeter `1 mm = 1000 μ`
    MM,
    /// centimeter `1 cm = 10 mm = 10_000 μ`
    CM,
    /// meter `100 cm = 1_000 mm = 1_000_000 μ`
    METER,
    /// kilometer `1 km = 1_000 m`
    KM,
    /// as exponent `10 ^ x`
    DYN(usize),
}

impl From<Unit> for Measure {
    fn from(unit: Unit) -> Self {
        Measure(unit.multiply())
    }
}

impl Unit {
    fn multiply(&self) -> i64 {
        use Unit::*;
        match self {
            MY => Measure::MY,
            MM => Measure::MY * 1_000,
            CM => Measure::MY * 10_000,
            METER => Measure::MY * 1_000_000,
            KM => Measure::MY * 1_000_000_000,
            DYN(p) => (0..*p).fold(1i64, |acc, _| acc * 10),
        }
    }
}

impl Measure {
    pub const MY: i64 = 10;
    pub const MM: Measure = Measure(1_000 * Self::MY);
    pub const ZERO: Measure = Measure(0);
    pub const MAX: Measure = Measure(1000000000000000000);
    pub const MIN: Measure = Measure(-1000000000000000000);

    pub fn as_i64(&self) -> i64 {
        self.0
    }

    #[inline]
    pub fn as_mm(&self) -> f64 {
        (self.0 as f64) / Unit::MM.multiply() as f64
    }

    /// Returns the value in the given `Unit`.   
    pub fn as_prec(&self, unit: Unit) -> f64 {
        (self.0 as f64) / unit.multiply() as f64
    }

    /// Rounds to the given Unit.
    pub fn round(&self, unit: Unit) -> Self {
        let val = if self.0 < 0 {
            self.0 - unit.multiply() / 2
        } else {
            self.0 + unit.multiply() / 2
        };
        let clip = val % unit.multiply();
        Measure(val - clip)
    }

    pub fn floor(&self, unit: Unit) -> Self {
        let val = self.0;
        let clip = val % unit.multiply();
        Measure(val - clip)
    }
}

macro_rules! measure_from_number {
    ($($typ:ident),+) => {
        $(
            impl From<$typ> for Measure {
                fn from(a: $typ) -> Self {
                    Self(a as i64)
                }
            }

            impl From<Measure> for $typ {
                fn from(a: Measure) -> Self {
                    a.0 as $typ
                }
            }

            impl Add<$typ> for Measure {
                type Output = Measure;

                fn add(self, rhs: $typ) -> Self::Output {
                    Self(self.0 + (rhs as i64))
                }
            }

            impl AddAssign<$typ> for Measure {
                fn add_assign(&mut self, rhs: $typ) {
                    self.0 += (rhs as i64);
                }
            }

            impl Sub<$typ> for Measure {
                type Output = Measure;

                fn sub(self, rhs: $typ) -> Self::Output {
                    Self(self.0 - (rhs as i64))
                }
            }

            impl Mul<$typ> for Measure {
                type Output = Measure;

                fn mul(self, rhs: $typ) -> Self::Output {
                    Self(self.0 * (rhs as i64))
                }
            }

            impl Div<$typ> for Measure {
                type Output = Measure;

                fn div(self, rhs: $typ) -> Self::Output {
                    Self(self.0 / (rhs as i64))
                }
            }
        )+
    }
}

measure_from_number!(u64, u32, u16, u8, usize, i64, i32, i16, i8, isize);

impl From<f64> for Measure {
    fn from(f: f64) -> Self {
        Self((f * Measure::MM.as_i64() as f64) as i64)
    }
}

impl From<Measure> for f64 {
    fn from(f: Measure) -> Self {
        f.0 as f64 / Measure::MM.as_i64() as f64
    }
}

impl TryFrom<&str> for Measure {
    type Error = ParseFloatError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Ok(Measure::from(value.parse::<f64>()?))
    }
}

impl TryFrom<String> for Measure {
    type Error = ParseFloatError;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        Ok(Measure::from(value.parse::<f64>()?))
    }
}

impl Display for Measure {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let p = f.precision().map(|p| p.min(4)).unwrap_or(4);
        if f.alternate() {
            Display::fmt(&self.0, f)
        } else {
            let mut s = self.round(Unit::DYN(4 - p)).0.abs().to_string();
            let len = 5 - s.len().min(5);
            (0..len).for_each(|_| s = String::from("0") + &s);
            if p > 0 {
                s.insert(s.len() - 4, '.');
            }
            s.truncate(s.len() - (4 - p));
            if self.0 < 0 {
                write!(f, "-{s}")
            } else {
                write!(f, "{s}")
            }
        }
    }
}

impl Debug for Measure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let val = self.0;
        let n = if val.is_negative() { 6 } else { 5 };
        let mut m = format!("{val:0n$}");
        m.insert(m.len() - 4, '.');
        write!(f, "Measure({})", m)
    }
}

impl Neg for Measure {
    type Output = Measure;

    fn neg(self) -> Self::Output {
        Self(-self.0)
    }
}

impl Add for Measure {
    type Output = Measure;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl AddAssign for Measure {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

impl Sub for Measure {
    type Output = Measure;

    fn sub(self, rhs: Self) -> Self::Output {
        Self(self.0 - rhs.0)
    }
}

impl SubAssign for Measure {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 -= rhs.0;
    }
}

impl Mul for Measure {
    type Output = Measure;

    fn mul(self, rhs: Self) -> Self::Output {
        Self(self.0 * rhs.0)
    }
}

impl Div for Measure {
    type Output = Measure;

    fn div(self, rhs: Self) -> Self::Output {
        Self(self.0 / rhs.0)
    }
}

impl Deref for Measure {
    type Target = i64;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl PartialOrd for Measure {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl Ord for Measure {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

#[cfg(test)]
mod should {
    use super::*;

    #[test]
    fn cmp() {
        let s1 = Measure(200000);
        let i1 = Measure(190000);
        let s2 = Measure::from(20.0);
        let i2 = Measure::from(19.0);

        assert!(s1 > i1);
        assert_eq!(s1.partial_cmp(&i1).unwrap(), Ordering::Greater);
        assert_eq!(s1, s1);
        assert_eq!(s1.partial_cmp(&s1).unwrap(), Ordering::Equal);

        assert!(s2 > i2);
        assert_eq!(s2.partial_cmp(&i2).unwrap(), Ordering::Greater);
        assert_eq!(s2, s1);
        assert_eq!(s2.partial_cmp(&s1).unwrap(), Ordering::Equal);

        assert_eq!(i1.cmp(&s1), Ordering::Less);
        assert_eq!(i1.cmp(&i1), Ordering::Equal);
    }

    #[test]
    fn round() {
        let m = Measure(1234567);
        assert_eq!(m.round(Unit::MY), Measure(1234570));
        assert_eq!(m.round(Unit::CM), Measure(1200000));
        assert_eq!(Measure(9_999_000).round(Unit::MM), Measure(10_000_000));
        assert_eq!(Measure::from(-0.4993).round(Unit::MM), Measure(0));
        assert_eq!(Measure::from(-0.4993).round(Unit::MY), Measure(-4990));
        let m = Measure::from(340.993);
        assert_eq!(Unit::DYN(0).multiply(), 1);
        assert_eq!(m.round(Unit::DYN(0)), Measure(3409930));
        assert_eq!(Unit::DYN(2).multiply(), 100);
        assert_eq!(m.round(Unit::DYN(2)), Measure(3409900));
        assert_eq!(Unit::DYN(3).multiply(), 1000);
        assert_eq!(m.round(Unit::DYN(3)), Measure(3410000));
    }

    #[test]
    fn display() {
        let m = Measure(12455);
        assert_eq!("1.2455", format!("{m}").as_str());
        assert_eq!("1.246", format!("{m:.3}").as_str());
        assert_eq!("1.2", format!("{m:.1}").as_str());
        assert_eq!("1.2455", format!("{m:.7}").as_str());
        assert_eq!("1", format!("{m:.0}").as_str());
        assert_eq!("-1.2455", format!("{:.7}", -m).as_str());
        let m = Measure(-455);
        assert_eq!("-0.0455", format!("{m}").as_str());
        assert_eq!("-0.3450", format!("{}", Measure(-3450)).as_str());
        assert_eq!("-455", format!("{m:#}").as_str());
        let m = Measure::from(4566.4689);
        assert_eq!(format!("{m:.3}"), "4566.469");
        let m = Measure::ZERO;
        assert_eq!(format!("{m:.2}"), "0.00");
    }

    #[test]
    fn min_max() {
        let max = Measure::MAX;
        let min = Measure::MIN;
        assert_eq!(max.to_string(), "100000000000000.0000");
        assert_eq!(min.to_string(), "-100000000000000.0000");
        assert_eq!(format!("{min:.0}"), "-100000000000000");
    }

    #[test]
    fn as_prec() {
        let m = Measure::from(12456.832);
        assert_eq!(m.as_prec(Unit::CM), 1245.6832);
        assert_eq!(m.as_prec(Unit::METER), 12.456832);
        let m = Measure::MAX;
        assert_eq!(m.as_prec(Unit::KM), 100_000_000f64);
    }
}
