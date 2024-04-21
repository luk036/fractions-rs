const gcd = require('num-integer').gcd;
const { Integer, Num, NumAssign, One, Signed, Zero } = require('num-traits');

function const_abs(a) {
    if (a < Zero::zero()) {
        return -a;
    } else {
        return a;
    }
}

function gcd_recur(m, n) {
    if (n == Zero::zero()) {
        return const_abs(m);
    } else {
        return gcd_recur(n, m % n);
    }
}

function const_gcd(m, n) {
    if (m == Zero::zero()) {
        return const_abs(n);
    } else {
        return gcd_recur(m, n);
    }
}

class Fraction {
    constructor(numer, denom) {
        this.numer = numer;
        this.denom = denom;
    }

    static new_raw(numer, denom) {
        return new Fraction(numer, denom);
    }

    numer() {
        return this.numer;
    }

    denom() {
        return this.denom;
    }

    static zero() {
        return new Fraction(Zero::zero(), One::one());
    }

    is_zero() {
        return this.numer.is_zero() && !this.denom.is_zero();
    }

    set_zero() {
        this.numer.set_zero();
        this.denom.set_one();
    }

    is_normal() {
        return !(this.numer.is_zero() || this.denom.is_zero());
    }

    is_infinite() {
        return !this.numer.is_zero() && this.denom.is_zero();
    }

    is_nan() {
        return this.numer.is_zero() && this.denom.is_zero();
    }

    static one() {
        return new Fraction(One::one(), One::one());
    }

    is_one() {
        return this.numer == this.denom;
    }

    set_one() {
        this.numer.set_one();
        this.denom.set_one();
    }

    normalize() {
        this.keep_denom_positive();
        return this.reduce();
    }

    abs() {
        if (this.is_negative()) {
            return -this;
        } else {
            return this;
        }
    }

    signum() {
        if (this.is_positive()) {
            return Fraction.one();
        } else if (this.is_zero()) {
            return Fraction.zero();
        } else {
            return -Fraction.one();
        }
    }

    is_positive() {
        return this.numer.is_positive();
    }

    is_negative() {
        return this.numer.is_negative();
    }

    reduce() {
        const common = gcd(this.numer, this.denom);
        if (common != One::one() && common != Zero::zero()) {
            this.numer /= common;
            this.denom /= common;
        }
        return common;
    }

    keep_denom_positive() {
        if (this.denom < Zero::zero()) {
            this.numer = -this.numer;
            this.denom = -this.denom;
        }
    }

    reciprocal() {
        [this.numer, this.denom] = [this.denom, this.numer];
        this.keep_denom_positive();
    }

    cross(rhs) {
        return this.numer * rhs.denom - this.denom * rhs.numer;
    }

    neg() {
        return new Fraction(-this.numer, this.denom);
    }

    inv() {
        let res = this;
        res.reciprocal();
        return res;
    }

    eq(other) {
        return this.denom == One::one() && this.numer == other;
    }

    partial_cmp(other) {
        if (this.denom == One::one() || other == Zero::zero()) {
            return this.numer.partial_cmp(other);
        }
        let lhs = new Fraction(this.numer, other);
        let rhs = this.denom;
        lhs.reduce();
        return lhs.numer.partial_cmp(lhs.denom * rhs);
    }

    cmp(other) {
        if (this.denom == other.denom) {
            return this.numer.cmp(other.numer);
        }
        let lhs = new Fraction(this.numer, other.numer);
        let rhs = new Fraction(this.denom, other.denom);
        lhs.reduce();
        rhs.reduce();
        return (lhs.numer * rhs.denom).cmp(lhs.denom * rhs.numer);
    }

    add_assign(other) {
        if (this.denom == other.denom) {
            this.numer += other.numer;
            this.reduce();
            return;
        }

        let rhs = other;
        [this.denom, rhs.numer] = [rhs.numer, this.denom];
        let common_n = this.reduce();
        let common_d = rhs.reduce();
        [this.denom, rhs.numer] = [rhs.numer, this.denom];
        this.numer = this.numer * rhs.denom + this.denom * rhs.numer;
        this.denom *= rhs.denom;
        [this.denom, common_d] = [common_d, this.denom];
        this.reduce();
        this.numer *= common_n;
        this.denom *= common_d;
        this.reduce();
    }

    sub_assign(other) {
        if (this.denom == other.denom) {
            this.numer -= other.numer;
            this.reduce();
            return;
        }

        let rhs = other;
        [this.denom, rhs.numer] = [rhs.numer, this.denom];
        let common_n = this.reduce();
        let common_d = rhs.reduce();
        [this.denom, rhs.numer] = [rhs.numer, this.denom];
        this.numer = this.cross(rhs);
        this.denom *= rhs.denom;
        [this.denom, common_d] = [common_d, this.denom];
        this.reduce();
        this.numer *= common_n;
        this.denom *= common_d;
        this.reduce();
    }

    mul_assign(other) {
        let rhs = other;
        [this.numer, rhs.numer] = [rhs.numer, this.numer];
        this.reduce();
        rhs.reduce();
        this.numer *= rhs.numer;
        this.denom *= rhs.denom;
    }

    div_assign(other) {
        let rhs = other;
        [this.denom, rhs.numer] = [rhs.numer, this.denom];
        this.normalize();
        rhs.reduce();
        this.numer *= rhs.denom;
        this.denom *= rhs.numer;
    }

    add(other) {
        let res = this;
        res.add_assign(other);
        return res;
    }

    sub(other) {
        let res = this;
        res.sub_assign(other);
        return res;
    }

    mul(other) {
        let res = this;
        res.mul_assign(other);
        return res;
    }

    div(other) {
        let res = this;
        res.div_assign(other);
        return res;
    }
}

module.exports = Fraction;



