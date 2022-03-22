use crate::{Measure, Unit};
use std::cmp::Ordering;
use std::convert::TryFrom;
use std::fmt::{Debug, Display, Formatter};
use std::num::{ParseFloatError, TryFromIntError};
use std::ops::{Add, AddAssign, Deref, Div, Mul, Neg, Sub, SubAssign};

///
/// # Measure32
///
/// A type to calculate lossless dimensions with a fixed precision.
/// All sizes are defined in the tenth fraction of `μ`:
///
///  * 10 = 1 μ
///  * 10_000  = 1 mm
///  * 10_000_000  = 1 m
///
/// The standard `Display::fmt`-methode represents the value in `mm`. The *alternate* Display
/// shows the `i32` value.
///
/// As 10_000 = 1 mm
///
/// ### Warning
/// Casting an `i64` into a `Measure32` can cause an `IntegerOverflow`-error similar to casting
/// a big `i64`-value into an `i32`. It's up to the programmer to omit these situation. Don't
/// try to store more then `+/- 214 meter` in a `Measure32`.
///
/// ### Example:
/// ```rust
///#     use allowance::Measure32;
///     let measure32 = Measure32::from(12.5);
///
///     assert_eq!(format!("{measure32}"),"12.5000");
///     assert_eq!(format!("{measure32:.2}"), "12.50");
///     assert_eq!(format!("{measure32:#}"), "125000");
/// ```
///
///

#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Measure32(i32);

impl Measure32 {
    pub const MY: i32 = 10;
    pub const MM: Measure32 = Measure32(1_000 * Self::MY);
    pub const ZERO: Measure32 = Measure32(0);
    /// Holds at maximum 214m
    pub const MAX: Measure32 = Measure32(i32::MAX);
    /// Holds at minimum -214m
    pub const MIN: Measure32 = Measure32(i32::MIN);

    pub fn as_i32(&self) -> i32 {
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
        if unit.multiply() == 0 {
            return *self;
        }
        let m = unit.multiply() as i32;
        let clip = self.0 % m;
        match m / 2 {
            _ if clip == 0 => *self, // don't round
            x if clip <= -x => Measure32(self.0 - clip - m),
            x if clip >= x => Measure32(self.0 - clip + m),
            _ => Measure32(self.0 - clip),
        }
    }

    pub fn floor(&self, unit: Unit) -> Self {
        let val = self.0;
        let clip = val % unit.multiply() as i32;
        Measure32(val - clip)
    }
}

macro_rules! measure32_from_number {
    ($($typ:ident),+) => {
        $(
            impl From<$typ> for Measure32 {
                fn from(a: $typ) -> Self {
                    Self(a as i32)
                }
            }

            impl From<Measure32> for $typ {
                fn from(a: Measure32) -> Self {
                    a.0 as $typ
                }
            }

            impl Add<$typ> for Measure32 {
                type Output = Measure32;

                fn add(self, rhs: $typ) -> Self::Output {
                    Self(self.0 + (rhs as i32))
                }
            }

            impl AddAssign<$typ> for Measure32 {
                fn add_assign(&mut self, rhs: $typ) {
                    self.0 += (rhs as i32);
                }
            }

            impl Sub<$typ> for Measure32 {
                type Output = Measure32;

                fn sub(self, rhs: $typ) -> Self::Output {
                    Self(self.0 - (rhs as i32))
                }
            }

            impl Mul<$typ> for Measure32 {
                type Output = Measure32;

                fn mul(self, rhs: $typ) -> Self::Output {
                    Self(self.0 * (rhs as i32))
                }
            }

            impl Div<$typ> for Measure32 {
                type Output = Measure32;

                fn div(self, rhs: $typ) -> Self::Output {
                    Self(self.0 / (rhs as i32))
                }
            }
        )+
    }
}

measure32_from_number!(u64, u32, u16, u8, usize, i64, i32, i16, i8);

impl From<f64> for Measure32 {
    fn from(f: f64) -> Self {
        Self((f * Measure32::MM.as_i32() as f64) as i32)
    }
}

impl From<Measure32> for f64 {
    fn from(f: Measure32) -> Self {
        f.0 as f64 / Measure32::MM.as_i32() as f64
    }
}

impl From<Measure32> for Measure {
    fn from(m: Measure32) -> Self {
        Measure::from(m.0)
    }
}

impl TryFrom<&str> for Measure32 {
    type Error = ParseFloatError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Ok(Measure32::from(value.parse::<f64>()?))
    }
}

impl TryFrom<String> for Measure32 {
    type Error = ParseFloatError;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        Ok(Measure32::from(value.parse::<f64>()?))
    }
}

impl TryFrom<Measure> for Measure32 {
    type Error = TryFromIntError;

    fn try_from(value: Measure) -> Result<Self, Self::Error> {
        let v: i32 = value.as_i64().try_into()?;
        Ok(Measure32(v))
    }
}

impl Display for Measure32 {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let p = f.precision().map(|p| p.min(4)).unwrap_or(4);
        if f.alternate() {
            Display::fmt(&self.0, f)
        } else {
            let val = self.round(Unit::DYN(4 - p)).0;
            let n = if val.is_negative() { 6 } else { 5 };
            let mut s = format!("{val:0n$}");
            if p > 0 {
                s.insert(s.len() - 4, '.');
            }
            s.truncate(s.len() - (4 - p));
            write!(f, "{s}")
        }
    }
}

impl Debug for Measure32 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let val = self.0;
        let n = if val.is_negative() { 6 } else { 5 };
        let mut m = format!("{val:0n$}");
        m.insert(m.len() - 4, '.');
        write!(f, "Measure32({})", m)
    }
}

impl Neg for Measure32 {
    type Output = Measure32;

    fn neg(self) -> Self::Output {
        Self(-self.0)
    }
}

impl Add for Measure32 {
    type Output = Measure32;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl Add<Measure> for Measure32 {
    type Output = Measure;

    fn add(self, rhs: Measure) -> Self::Output {
        Measure::from(rhs.as_i64() + self.as_i32() as i64)
    }
}

impl AddAssign for Measure32 {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

impl Sub for Measure32 {
    type Output = Measure32;

    fn sub(self, rhs: Self) -> Self::Output {
        Self(self.0 - rhs.0)
    }
}

impl SubAssign for Measure32 {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 -= rhs.0;
    }
}

impl Mul for Measure32 {
    type Output = Measure32;

    fn mul(self, rhs: Self) -> Self::Output {
        Self(self.0 * rhs.0)
    }
}

impl Div for Measure32 {
    type Output = Measure32;

    fn div(self, rhs: Self) -> Self::Output {
        Self(self.0 / rhs.0)
    }
}

impl Deref for Measure32 {
    type Target = i32;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl PartialOrd for Measure32 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl Ord for Measure32 {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

#[cfg(test)]
mod should {
    use super::*;

    #[test]
    fn cmp() {
        let s1 = Measure32(200000);
        let i1 = Measure32(190000);
        let s2 = Measure32::from(20.0);
        let i2 = Measure32::from(19.0);

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
    fn neg() {
        let m = -Measure32(232332);
        let n = Measure32(-232332);
        assert_eq!(n.0, m.0);
        assert_eq!(n, m);
    }

    #[test]
    fn round() {
        let m = Measure32(1234567);
        assert_eq!(Measure32(1234570), m.round(Unit::MY));
        assert_eq!(Measure32(1200000), m.round(Unit::CM));
        assert_eq!(Measure32(10_000_000), Measure32(9_999_000).round(Unit::MM));
        assert_eq!(Measure32(0), Measure32::from(-0.4993).round(Unit::MM));
        assert_eq!(Measure32(-4990), Measure32::from(-0.4993).round(Unit::MY));
        assert_eq!(Measure32(-10000), Measure32::from(-5000).round(Unit::MM));
        let m = Measure32::from(340.993);
        assert_eq!(10, Unit::DYN(1).multiply());
        assert_eq!(Measure32(3409930), m.round(Unit::DYN(1)));
        assert_eq!(100, Unit::DYN(2).multiply());
        assert_eq!(Measure32(3409900), m.round(Unit::DYN(2)));
        assert_eq!(1000, Unit::DYN(3).multiply());
        assert_eq!(Measure32(3410000), m.round(Unit::DYN(3)));
        assert_eq!(Measure32(3400000), m.floor(Unit::DYN(4)));
        assert_eq!(-340.000, -340.993_f64.floor());
        assert_eq!(
            Measure32(-3400000),
            Measure32::from(-340.993).floor(Unit::DYN(4))
        );
    }

    #[test]
    fn display() {
        let m = Measure32(12455);
        assert_eq!("1.2455", format!("{m}").as_str());
        assert_eq!("1.246", format!("{m:.3}").as_str());
        assert_eq!("1.2", format!("{m:.1}").as_str());
        assert_eq!("1.2455", format!("{m:.7}").as_str());
        assert_eq!("1", format!("{m:.0}").as_str());
        assert_eq!("-1.2455", format!("{:.7}", -m).as_str());
        let m = Measure32(-455);
        assert_eq!("-0.0455", format!("{m}").as_str());
        assert_eq!("-0.3450", format!("{}", Measure32(-3450)).as_str());
        assert_eq!("-455", format!("{m:#}").as_str());
        let m = Measure32::from(4566.4689);
        assert_eq!(format!("{m:.3}"), "4566.469");
        let m = Measure32::ZERO;
        assert_eq!(format!("{m:.2}"), "0.00");
    }

    #[test]
    fn min_max() {
        let max = Measure32::MAX;
        let min = Measure32::MIN;

        assert_eq!(max.0, 2147483647);
        assert_eq!(min.0, -2147483648);
        assert_eq!(format!("{max:.0}"), "214748");
    }

    #[test]
    fn as_prec() {
        let m = Measure32::from(12456.832);
        assert_eq!(m.as_prec(Unit::CM), 1245.6832);
        assert_eq!(m.as_prec(Unit::METER), 12.456832);
    }
}
