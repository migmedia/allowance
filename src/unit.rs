use super::Measure;
use std::ops::Mul;

#[derive(Debug)]
pub enum Unit {
    /// My-meter `μ` the equivalent to `DYN(1)`.
    MY,
    /// Millimeter `1 mm = 1000 μ` the equivalent to `DYN(4)`.
    MM,
    /// Centimeter `1 cm = 10 mm = 10_000 μ` the equivalent to `DYN(5)`.
    CM,
    /// Inch `1 in = 25.4 mm = 25_400 μ`.
    INCH,
    /// Foot `1 ft = 12 in = 304.8 mm = 304_800 μ`.
    FT,
    /// Yard `1 yd = 3 ft = 914.4 mm = 914_400 μ`.
    YD,
    /// Meter `100 cm = 1_000 mm = 1_000_000 μ` the equivalent to `DYN(7)`.
    METER,
    /// Kilometer `1 km = 1_000 m` the equivalent to `DYN(10)`.
    KM,
    /// Mile `1 mi = 1760 yd = 1609.344 m = 1_609_344_000 μ`.
    MILE,
    /// As exponent `10 ^ x`.  
    DYN(usize),
}

impl Unit {
    #[inline]
    pub fn multiply(&self) -> i64 {
        use Unit::*;
        match self {
            MY => Measure::MY,
            MM => Measure::MY * 1_000,
            CM => Measure::MY * 10_000,
            INCH => Measure::MY * 25_400,
            FT => Measure::MY * 304_800,
            YD => Measure::MY * 914_400,
            METER => Measure::MY * 1_000_000,
            KM => Measure::MY * 1_000_000_000,
            MILE => Measure::MY * 1_609_344_000,
            DYN(p) => (0..*p).fold(1i64, |acc, _| acc * 10),
        }
    }
}

impl PartialEq for Unit {
    fn eq(&self, other: &Self) -> bool {
        self.multiply() == other.multiply()
    }
}

macro_rules! unit_from_number {
    ($($typ:ident),+) => {
        $(
            impl Mul<$typ> for Unit {
                type Output = Measure;

                fn mul(self, rhs: $typ) -> Self::Output {
                    Measure::from(self.multiply() * rhs as i64)
                }
            }

             impl Mul<Unit> for $typ {
                type Output = Measure;

                fn mul(self, rhs: Unit) -> Self::Output {
                    Measure::from(rhs.multiply() * self as i64)
                }
            }
        )+
    }
}

unit_from_number!(i8, i16, i32, i64, u8, u16, u32, u64);

#[cfg(test)]
mod should {
    use crate::{Measure, Unit};

    #[test]
    fn multiply_with_number() {
        assert_eq!(Measure::from(3.0), 3 * Unit::MM);
        assert_eq!(Measure::from(55000.0), 55 * Unit::METER);
    }

    #[test]
    fn be_equal_dyn() {
        assert_eq!(Unit::MY.multiply(), Unit::DYN(1).multiply());
        assert_eq!(Unit::MM.multiply(), Unit::DYN(4).multiply());
        assert_eq!(Unit::METER, Unit::DYN(7));
    }
}
