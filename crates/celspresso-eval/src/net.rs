//! The network extension (`ip`, `cidr`, `net.IP`, `net.CIDR`), following the
//! Kubernetes CEL library. IPv6 zones and IPv4-mapped IPv6 addresses are rejected.

use std::fmt;
use std::net::IpAddr;

/// A value of one of the opaque network types.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Net {
    Ip(IpAddr),
    /// The address as written (not masked) and the prefix length.
    Cidr(IpAddr, u8),
}

impl Net {
    pub fn type_name(&self) -> &'static str {
        match self {
            Net::Ip(_) => "net.IP",
            Net::Cidr(..) => "net.CIDR",
        }
    }
}

impl fmt::Display for Net {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Net::Ip(a) => write!(f, "{a}"),
            Net::Cidr(a, n) => write!(f, "{a}/{n}"),
        }
    }
}

pub fn parse_ip(s: &str) -> Result<IpAddr, String> {
    if s.contains('%') {
        return Err("IP Address with zone value is not allowed".into());
    }
    let a: IpAddr = s.parse().map_err(|_| format!("IP Address '{s}' parse error during conversion from string"))?;
    reject_mapped(a)
}

pub fn parse_cidr(s: &str) -> Result<Net, String> {
    if s.contains('%') {
        return Err("CIDR with zone value is not allowed".into());
    }
    let bad = || format!("network address parse error during conversion from string: '{s}'");
    let (addr, len) = s.split_once('/').ok_or_else(bad)?;
    let a: IpAddr = addr.parse().map_err(|_| bad())?;
    let a = reject_mapped(a)?;
    let n: u8 = len.parse().map_err(|_| bad())?;
    if n > bits(&a) || len.starts_with('+') {
        return Err(bad());
    }
    Ok(Net::Cidr(a, n))
}

fn reject_mapped(a: IpAddr) -> Result<IpAddr, String> {
    match a {
        IpAddr::V6(v6) if v6.to_ipv4_mapped().is_some() => Err("IPv4-mapped IPv6 address is not allowed".into()),
        a => Ok(a),
    }
}

fn bits(a: &IpAddr) -> u8 {
    if a.is_ipv4() {
        32
    } else {
        128
    }
}

fn as_u128(a: &IpAddr) -> u128 {
    match a {
        IpAddr::V4(v4) => u128::from(u32::from(*v4)),
        IpAddr::V6(v6) => u128::from(*v6),
    }
}

fn from_u128(v: u128, like: &IpAddr) -> IpAddr {
    match like {
        IpAddr::V4(_) => IpAddr::V4((v as u32).into()),
        IpAddr::V6(_) => IpAddr::V6(v.into()),
    }
}

/// The network address of `a/n`: host bits cleared.
pub fn masked(a: &IpAddr, n: u8) -> IpAddr {
    let total = bits(a);
    let host = u32::from(total - n);
    let mask = if host >= 128 { 0 } else { !0u128 << host };
    let width_mask = if total == 128 { !0u128 } else { (1u128 << total) - 1 };
    from_u128(as_u128(a) & mask & width_mask, a)
}

pub fn contains_ip(net: &IpAddr, n: u8, ip: &IpAddr) -> bool {
    net.is_ipv4() == ip.is_ipv4() && masked(net, n) == masked(ip, n)
}

pub fn contains_cidr(net: &IpAddr, n: u8, other: &IpAddr, m: u8) -> bool {
    m >= n && contains_ip(net, n, other)
}

pub fn is_canonical(s: &str) -> Result<bool, String> {
    Ok(parse_ip(s)?.to_string() == s)
}

pub fn is_global_unicast(a: &IpAddr) -> bool {
    match a {
        IpAddr::V4(v4) => !(v4.is_unspecified() || v4.is_loopback() || v4.is_multicast() || v4.is_link_local() || v4.is_broadcast()),
        IpAddr::V6(v6) => !(v6.is_unspecified() || v6.is_loopback() || v6.is_multicast() || is_link_local_unicast(a)),
    }
}

pub fn is_link_local_unicast(a: &IpAddr) -> bool {
    match a {
        IpAddr::V4(v4) => v4.is_link_local(),
        IpAddr::V6(v6) => v6.segments()[0] & 0xffc0 == 0xfe80,
    }
}

pub fn is_link_local_multicast(a: &IpAddr) -> bool {
    match a {
        IpAddr::V4(v4) => v4.octets()[..3] == [224, 0, 0],
        IpAddr::V6(v6) => v6.segments()[0] & 0xff0f == 0xff02,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parsing_and_masks() {
        assert!(parse_ip("fe80::1%en0").unwrap_err().contains("zone"));
        assert!(parse_ip("::ffff:1.2.3.4").unwrap_err().contains("mapped"));
        assert!(parse_cidr("10.0.0.0/33").is_err());
        assert!(parse_cidr("10.0.0.0/").is_err());
        let Net::Cidr(a, n) = parse_cidr("192.168.7.9/20").unwrap() else { panic!() };
        assert_eq!(masked(&a, n).to_string(), "192.168.0.0");
        assert_eq!(masked(&a, 0).to_string(), "0.0.0.0");
        let Net::Cidr(b, m) = parse_cidr("2001:db8::/32").unwrap() else { panic!() };
        assert!(contains_ip(&b, m, &parse_ip("2001:db8::1").unwrap()));
        assert!(!contains_ip(&b, m, &parse_ip("10.0.0.1").unwrap()));
        assert!(contains_cidr(&b, m, &b, 33));
        assert!(!contains_cidr(&b, m, &b, 31));
        assert!(is_canonical("2001:db8::68").unwrap());
        assert!(!is_canonical("2001:DB8::68").unwrap());
    }
}
