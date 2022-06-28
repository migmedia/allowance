use crate::{Measure, Measure32, Unit};
use std::cmp::Ordering;
use std::convert::TryFrom;
use std::fmt::{Debug, Display, Formatter};
use std::num::{ParseFloatError, TryFromIntError};
use std::ops::{Add, AddAssign, Deref, Div, Mul, Neg, Sub, SubAssign};

///
/// # Measure16
///
/// A type to calculate lossless dimensions with a fixed precision.
/// All sizes are defined in the tenth fraction of `μ`:
///
///  * 10 = 1 μ
///  * 10_000  = 1 mm
///  * 30_000  = 3 mm
///
/// The standard `Display::fmt`-methode represents the value in `mm`. The *alternate* Display
/// shows the `i16` value.
///
/// As 10_000 = 1 mm
///
/// ### Warning
/// Casting an `i64` into a `Measure16` can cause an `IntegerOverflow`-error similar to casting
/// a big `i64`-value into an `i16`. It's up to the programmer to omit these situation.
///
/// If your sizes can exceed 3 mm, than this type is __not__ for you. Again:   
///
/// **Don't try to store more then +/- 3 millimeter in a** `Measure16`.
///
/// ### Example:
/// ```rust
///#     use allowance::Measure16;
///     let Measure16 = Measure16::from(1.5);
///
///     assert_eq!(format!("{Measure16}"),"1.5000");
///     assert_eq!(format!("{Measure16:.2}"), "1.50");
///     assert_eq!(format!("{Measure16:#}"), "15000");
/// ```
///
///

#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Measure16(i16);

impl Measure16 {
    pub const MY: i16 = 10;
    pub const MM: Measure16 = Measure16(1_000 * Self::MY);
    pub const ZERO: Measure16 = Measure16(0);
    /// Holds at maximum 3mm
    pub const MAX: Measure16 = Measure16(i16::MAX);
    /// Holds at minimum -3mm
    pub const MIN: Measure16 = Measure16(i16::MIN);

    pub fn as_i16(&self) -> i16 {
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
        let clip = (self.0 % m as i16) as i32;
        match m / 2 {
            _ if clip == 0 => *self, // don't round
            x if clip <= -x => Measure16::from(self.0 as i32 - clip - m),
            x if clip >= x => Measure16::from(self.0 as i32 - clip + m),
            _ => Measure16(self.0 - clip as i16),
        }
    }

    pub fn floor(&self, unit: Unit) -> Self {
        let val = self.0;
        let clip = val % unit.multiply() as i16;
        Measure16(val - clip)
    }
}

macro_rules! Measure16_from_number {
    ($($typ:ident),+) => {
        $(
            impl From<$typ> for Measure16 {
                fn from(a: $typ) -> Self {
                    assert!(a < i16::MAX as $typ && a > i16::MIN as $typ);
                    Self(a as i16)
                }
            }

            impl From<Measure16> for $typ {
                fn from(a: Measure16) -> Self {
                    a.0 as $typ
                }
            }

            impl Add<$typ> for Measure16 {
                type Output = Measure16;

                fn add(self, rhs: $typ) -> Self::Output {
                    Self(self.0 + (rhs as i16))
                }
            }

            impl AddAssign<$typ> for Measure16 {
                fn add_assign(&mut self, rhs: $typ) {
                    self.0 += (rhs as i16);
                }
            }

            impl Sub<$typ> for Measure16 {
                type Output = Measure16;

                fn sub(self, rhs: $typ) -> Self::Output {
                    Self(self.0 - (rhs as i16))
                }
            }

            impl Mul<$typ> for Measure16 {
                type Output = Measure16;

                fn mul(self, rhs: $typ) -> Self::Output {
                    Self(self.0 * (rhs as i16))
                }
            }

            impl Div<$typ> for Measure16 {
                type Output = Measure16;

                fn div(self, rhs: $typ) -> Self::Output {
                    Self(self.0 / (rhs as i16))
                }
            }
        )+
    }
}

Measure16_from_number!(u64, u32, u16, u8, usize, i64, i32, i16, i8);

impl From<Unit> for Measure16 {
    fn from(unit: Unit) -> Self {
        Measure16::from(unit.multiply())
    }
}

impl From<f64> for Measure16 {
    fn from(f: f64) -> Self {
        assert!(
            f < i16::MAX as f64 && f > i16::MIN as f64,
            "i16 overflow, the f64 is beyond the limits of this type (Measure16)."
        );
        Self((f * Measure16::MM.as_i16() as f64) as i16)
    }
}

impl From<Measure16> for f64 {
    fn from(f: Measure16) -> Self {
        f.0 as f64 / Measure16::MM.as_i16() as f64
    }
}

// Upcasting is no problem!
impl From<Measure16> for Measure {
    fn from(m: Measure16) -> Self {
        Measure::from(m.0)
    }
}

// Upcasting is no problem!
impl From<Measure16> for Measure32 {
    fn from(m: Measure16) -> Self {
        Measure32::from(m.0)
    }
}

impl TryFrom<&str> for Measure16 {
    type Error = ParseFloatError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Ok(Measure16::from(value.parse::<f64>()?))
    }
}

impl TryFrom<String> for Measure16 {
    type Error = ParseFloatError;

    fn try_from(value: String) -> Result<Self, Self::Error> {
        Ok(Measure16::from(value.parse::<f64>()?))
    }
}

impl TryFrom<Measure> for Measure16 {
    type Error = TryFromIntError;

    fn try_from(value: Measure) -> Result<Self, Self::Error> {
        let v: i16 = value.as_i64().try_into()?;
        Ok(Measure16(v))
    }
}

impl TryFrom<Measure32> for Measure16 {
    type Error = TryFromIntError;

    fn try_from(value: Measure32) -> Result<Self, Self::Error> {
        let v: i16 = value.as_i32().try_into()?;
        Ok(Measure16(v))
    }
}

impl Display for Measure16 {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let p = f.precision().map(|p| p.min(4)).unwrap_or(4);
        assert!(p <= 4, "Measure has a limited precision of 4!");
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

impl Debug for Measure16 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let val = self.0;
        let n = if val.is_negative() { 6 } else { 5 };
        let mut m = format!("{val:0n$}");
        m.insert(m.len() - 4, '.');
        write!(f, "Measure16({})", m)
    }
}

impl Neg for Measure16 {
    type Output = Measure16;

    fn neg(self) -> Self::Output {
        Self(-self.0)
    }
}

impl Add for Measure16 {
    type Output = Measure16;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl Add<Measure> for Measure16 {
    type Output = Measure;

    fn add(self, rhs: Measure) -> Self::Output {
        Measure::from(rhs.as_i64() + self.as_i16() as i64)
    }
}

impl Add<Measure32> for Measure16 {
    type Output = Measure32;

    fn add(self, rhs: Measure32) -> Self::Output {
        Measure32::from(rhs.as_i32() + self.as_i16() as i32)
    }
}

impl Add<Measure16> for Measure32 {
    type Output = Measure32;

    fn add(self, rhs: Measure16) -> Self::Output {
        Measure32::from(rhs.as_i16() as i32 + self.as_i32())
    }
}

impl AddAssign for Measure16 {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

impl Sub for Measure16 {
    type Output = Measure16;

    fn sub(self, rhs: Self) -> Self::Output {
        Self(self.0 - rhs.0)
    }
}

impl Sub<Measure32> for Measure16 {
    type Output = Measure32;

    fn sub(self, rhs: Measure32) -> Self::Output {
        Measure32::from(self.0 as i32 - rhs.as_i32())
    }
}

impl Sub<Measure> for Measure16 {
    type Output = Measure;

    fn sub(self, rhs: Measure) -> Self::Output {
        Measure::from(self.0 as i64 - rhs.as_i64())
    }
}

impl SubAssign for Measure16 {
    fn sub_assign(&mut self, rhs: Self) {
        self.0 -= rhs.0;
    }
}

impl Mul for Measure16 {
    type Output = Measure16;

    fn mul(self, rhs: Self) -> Self::Output {
        Self(self.0 * rhs.0)
    }
}

impl Div for Measure16 {
    type Output = Measure16;

    fn div(self, rhs: Self) -> Self::Output {
        Self(self.0 / rhs.0)
    }
}

impl Deref for Measure16 {
    type Target = i16;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl PartialOrd for Measure16 {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }
}

impl Ord for Measure16 {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

#[cfg(test)]
mod should {
    use super::*;

    #[test]
    fn cmp() {
        let s1 = Measure16(20000);
        let i1 = Measure16(19000);
        let s2 = Measure16::from(2.0);
        let i2 = Measure16::from(1.9);

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
        let m = -Measure16(2323);
        let n = Measure16(-2323);
        assert_eq!(n.0, m.0);
        assert_eq!(n, m);
    }

    #[test]
    fn round() {
        let m = Measure16(12345);
        assert_eq!(Measure16(12350), m.round(Unit::MY));
        assert_eq!(Measure16(10_000), m.round(Unit::MM));
        assert_eq!(Measure16(10_000), Measure16(9_000).round(Unit::MM));
        assert_eq!(Measure16(0), Measure16::from(-0.4993).round(Unit::MM));
        assert_eq!(Measure16(-4990), Measure16::from(-0.4993).round(Unit::MY));
        assert_eq!(Measure16(-10000), Measure16::from(-5000).round(Unit::MM));
        let m = Measure16::from(2.993);
        assert_eq!(10, Unit::DYN(1).multiply());
        assert_eq!(Measure16(29930), m.round(Unit::DYN(1)));
        assert_eq!(100, Unit::DYN(2).multiply());
        assert_eq!(Measure16(29900), m.round(Unit::DYN(2)));
        assert_eq!(1000, Unit::DYN(3).multiply());
        assert_eq!(Measure16(30000), m.round(Unit::DYN(3)));
        assert_eq!(Measure16(20000), m.floor(Unit::DYN(4)));
        assert_eq!(
            Measure16(-20000),
            Measure16::from(-2.293).floor(Unit::DYN(4))
        );
    }

    #[test]
    fn display() {
        let m = Measure16(12455);
        assert_eq!("1.2455", format!("{m}").as_str());
        assert_eq!("1.246", format!("{m:.3}").as_str());
        assert_eq!("1.2", format!("{m:.1}").as_str());
        assert_eq!("1.2455", format!("{m:.7}").as_str());
        assert_eq!("1", format!("{m:.0}").as_str());
        assert_eq!("-1.2455", format!("{:.7}", -m).as_str());
        let m = Measure16(-455);
        assert_eq!("-0.0455", format!("{m}").as_str());
        assert_eq!("-0.3450", format!("{}", Measure16(-3450)).as_str());
        assert_eq!("-455", format!("{m:#}").as_str());
        let m = Measure16::from(1.4689);
        assert_eq!(format!("{m:.3}"), "1.469");
        let m = Measure16::ZERO;
        assert_eq!(format!("{m:.2}"), "0.00");
    }

    #[test]
    fn min_max() {
        let max = Measure16::MAX;
        let min = Measure16::MIN;

        assert_eq!(max.0, 32767);
        assert_eq!(min.0, -32768);
        assert_eq!(format!("{max:.0}"), "3");
    }

    #[test]
    fn as_prec() {
        let m = Measure16::from(0.832);
        assert_eq!(m.as_prec(Unit::CM), 0.0832);
        assert_eq!(m.as_prec(Unit::MY), 832.0);
    }
}
