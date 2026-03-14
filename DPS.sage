import random
import hashlib
import string
import time
import csv
import base64
from kyber_py.kyber import Kyber512

# PARAMETERS
q = 35184372067549
n = 512
k = 4
l = 4
d = 15
d_prime = 7
eta = 7
beta = 322
n1c = 46
gamma = 905679
gamma1 = 905679
gamma2 = 905679
seedbytes = 32

P.<t> = PolynomialRing(Integers(q))
Rq.<x> = QuotientRing(P, P.ideal(t^n + 1))


def apply_poly(f, *args):
    return Rq(sum([f(*(int(coeff) for coeff in coeffs), args[-1]) * x^i for i, coeffs in enumerate(zip(*(poly.list() for poly in args[:-1])))]))


def apply_polyvec(f, *args):
    return vector([apply_poly(f, *polys, args[-1]) for polys in zip(*args[:-1])])


def centered_mod(r, a):
    r_cmod_a = r % a
    if r_cmod_a > a // 2:
        r_cmod_a -= a
    return r_cmod_a


def sample_matrix_unif(rows, cols, a, b):
    return Matrix([[Rq(sum([random.randint(a, b) * x^i for i in range(n)])) for i_ in range(cols)] for j_ in range(rows)])


def sample_vector_unif(dim, a, b):
    return vector([Rq(sum([random.randint(a, b) * x^i for i in range(n)])) for i_ in range(dim)])


def sample_matrix_hash(rows, cols, a, b, r):
    chash = hashlib.sha256()
    chash.update(r)
    random.seed(int(chash.digest().hex(), 16))
    return Matrix([[Rq(sum([random.randint(a, b) * x^i for i in range(n)])) for i_ in range(cols)] for j_ in range(rows)])


def sample_vector_hash(dim, a, b, pk, tau):
    chash = hashlib.sha256()
    chash.update(bytes(coeff_byte for poly in pk for coeff in poly for coeff_byte in int(coeff).to_bytes(8, byteorder="big")))
    chash.update(tau)
    random.seed(int(chash.digest().hex(), 16))
    return vector([Rq(sum([random.randint(a, b) * x^i for i in range(n)])) for i_ in range(dim)])


def sample_challenge_hash(msg, polyvec, pk):
    chash = hashlib.sha256()
    chash.update(bytes(msg, "utf-8"))
    chash.update(bytes(coeff_byte for poly in polyvec for coeff in poly for coeff_byte in int(coeff).to_bytes(8, byteorder="big")))
    chash.update(bytes(coeff_byte for poly in pk for coeff in poly for coeff_byte in int(coeff).to_bytes(8, byteorder="big")))
    random.seed(int(chash.digest().hex(), 16))
    c_list = random.sample([0] * (n - n1c) + random.choices([-1, 1], k=n1c), n)
    return Rq(sum([c_list[i] * x^i for i in range(n)]))


def power2round(r, u):
    r = r % q
    r0 = centered_mod(r, 2^u)
    return (r - r0) // (2^u)


def decompose(r, alpha):
    r = r % q
    r0 = centered_mod(r, alpha)
    if r - r0 == q - 1:
        r1 = 0
        r0 = r0 - 1
    else:
        r1 = (r - r0) // alpha
        return r1, r0


def highbits(r, alpha):
    r1, r0 = decompose(r, alpha)
    return r1


def lowbits(r, alpha):
    r1, r0 = decompose(r, alpha)
    return r0


def makehint(z, r, alpha):
    r1 = highbits(r, alpha)
    v1 = highbits(r + z, alpha)
    return r1 != v1


def usehint(h, r, alpha):
    m = (q - 1) // alpha
    r1, r0 = decompose(r, alpha)
    if h == 1 and r0 > 0:
        return (r1 + 1) % m
    if h == 1 and r0 <= 0:
        return (r1 - 1) % m
    return r1


def power2round_polyvec(r, u):
    return apply_polyvec(power2round, r, u)


def decompose_polyvec(r, alpha):
    return apply_polyvec(decompose, r, alpha)


def highbits_polyvec(r, alpha):
    return apply_polyvec(highbits, r, alpha)


def lowbits_polyvec(r, alpha):
    return apply_polyvec(lowbits, r, alpha)


def makehint_polyvec(z, r, alpha):
    return apply_polyvec(makehint, z, r, alpha)


def usehint_polyvec(h, r, alpha):
    return apply_polyvec(usehint, h, r, alpha)


def infinity_norm_mod(r):
    return abs(centered_mod(lift(r), q))


def infinity_norm_poly(poly):
    return max(infinity_norm_mod(r) for r in poly)


def infinity_norm_polyvec(polyvec):
    return max(infinity_norm_poly(poly) for poly in polyvec)


def encode_dilithium_t1(t1):
    return bytes(coeff_byte for poly in t1 for coeff in poly for coeff_byte in int(coeff % q).to_bytes(6, byteorder="little"))


class DilithiumQROM:
    @staticmethod
    def keygen():
        rho = bytes(random.getrandbits(8) for i in range(8))
        A = sample_matrix_hash(k, l, 0, q - 1, rho)
        K = bytes(random.getrandbits(8) for i in range(seedbytes))
        s1 = sample_vector_unif(l, -eta, eta)
        s2 = sample_vector_unif(k, -eta, eta)
        t = A * s1 + s2
        t1 = power2round_polyvec(t, d)
        t0 = t - (t1 * (2^d))
        pk = (A, rho, t1)
        sk = (rho, s1, s2, t0, K)
        return pk, sk

    @staticmethod
    def sign(sk, m):
        rho, s1, s2, t0, K = sk
        A = sample_matrix_hash(k, l, 0, q - 1, rho)
        kappa = 0
        z, h = "perp", "perp"
        while z == "perp" and h == "perp":
            kappa = kappa + 1
            y = sample_vector_unif(l, -gamma2 + 1, gamma2 - 1)
            w = A * y
            w1 = highbits_polyvec(w, 2 * gamma1)
            c = sample_challenge_hash(m, w1, w1)
            z = y + c * s1
            if infinity_norm_polyvec(z) >= gamma2 - beta or infinity_norm_polyvec(lowbits_polyvec(w - c * s2, 2 * gamma1)) >= gamma1 - beta:
                z, h = "perp", "perp"
            else:
                h = makehint_polyvec(-1 * c * t0, w - c * s2 + c * t0, 2 * gamma1)
        return z, h, c

    @staticmethod
    def verify(pk, M, sigma):
        A, rho, t1 = pk
        z, h, c = sigma
        w1_p = usehint_polyvec(h, A * z - c * t1 * (2^d), 2 * gamma1)
        return infinity_norm_polyvec(z) < gamma2 - beta and c == sample_challenge_hash(M, w1_p, w1_p)


class ARKG:
    @staticmethod
    def keyGen():
        pk_kem, sk_kem = Kyber512.keygen()
        rho = bytes(random.getrandbits(8) for i in range(8))
        A = sample_matrix_hash(k, l, 0, q - 1, rho)
        K = bytes(random.getrandbits(8) for i in range(seedbytes))
        s1_p = sample_vector_unif(l, -eta, eta)
        s2_p = sample_vector_unif(k, -eta, eta)
        t_p = A * s1_p + s2_p
        t1_p = power2round_polyvec(t_p, d)
        t1_p_bar = power2round_polyvec(t_p, d_prime - 1)
        t0_p = t_p - (apply_polyvec(lambda a, b: a // b, t1_p, 2) * (2^d))
        pkpS = (rho, t1_p, t1_p_bar)
        skpS = (rho, s1_p, s2_p, t0_p, K)
        return pk_kem, sk_kem, pkpS, skpS

    @staticmethod
    def derivePk(pkpS, pk_kem):
        tau, v = Kyber512.encaps(pk_kem)
        rho, t1_p, t1_p_bar = pkpS
        A = sample_matrix_hash(k, l, 0, q - 1, rho)
        s1_p_prime = sample_vector_hash(l, -eta, eta, t1_p_bar, tau)
        s2_p_prime = sample_vector_hash(k, -eta, eta, t1_p_bar, tau)
        t_p_prime = A * s1_p_prime + s2_p_prime
        t1_p_prime = power2round_polyvec(t_p_prime, d_prime - 1)
        t1_tau = t1_p_prime + t1_p_bar
        pk_tau = (rho, t1_tau)
        cred = v
        return pk_tau, cred

    @staticmethod
    def deriveSk(cred, pkpS, skpS, sk_kem):
        rho, t1_p, t1_p_bar = pkpS
        A = sample_matrix_hash(k, l, 0, q - 1, rho)
        rho, s1_p, s2_p, t0_p, K = skpS
        tau = Kyber512.decaps(sk_kem, cred)
        s1_p_prime = sample_vector_hash(l, -eta, eta, t1_p_bar, tau)
        s2_p_prime = sample_vector_hash(k, -eta, eta, t1_p_bar, tau)
        s1_tau = s1_p_prime + s1_p
        s2_tau = s2_p_prime + s2_p
        t_tau = A * s1_tau + s2_tau
        t1_tau = power2round_polyvec(t_tau, d_prime)
        t0_tau = t_tau - (t1_tau * (2^d_prime))
        return rho, s1_tau, s2_tau, t0_tau, K


class DPS:
    @staticmethod
    def dKeyGen():
        pkdS, skdS = DilithiumQROM.keygen()
        return pkdS, skdS

    @staticmethod
    def pKeyGen():
        pk_kem, sk_kem, pkpS, skpS = ARKG.keyGen()
        return pk_kem, sk_kem, pkpS, skpS

    @staticmethod
    def delegate(pkpS, pk_kem, skdS):
        pk_tau, cred = ARKG.derivePk(pkpS, pk_kem)
        rho, t1_tau = pk_tau
        t1_bytes = encode_dilithium_t1(t1_tau)
        pk_tau_message = base64.b64encode(t1_bytes).decode("utf-8")
        sigma_tau = DilithiumQROM.sign(skdS, pk_tau_message)
        ddata = cred
        warr = (pk_tau, sigma_tau)
        return ddata, warr

    @staticmethod
    def proxySign(skpS, pkpS, warr, ddata, sk_kem, m):
        rho, s1_tau, s2_tau, t0_tau, K = ARKG.deriveSk(ddata, pkpS, skpS, sk_kem)
        pk_tau, _ = warr
        rho, t1_tau = pk_tau
        A = sample_matrix_hash(k, l, 0, q - 1, rho)
        kappa = 0
        z, h = "perp", "perp"
        while z == "perp" and h == "perp":
            kappa = kappa + 1
            y = sample_vector_unif(l, -gamma + 1, gamma - 1)
            w = A * y
            w1 = highbits_polyvec(w, 2 * gamma)
            c = sample_challenge_hash(m, w1, t1_tau)
            z = y + c * s1_tau
            if infinity_norm_polyvec(z) >= gamma - 2 * beta or infinity_norm_polyvec(lowbits_polyvec(w - c * s2_tau, 2 * gamma)) >= gamma - 2 * beta:
                z, h = "perp", "perp"
            else:
                h = makehint_polyvec(-1 * c * t0_tau, w - c * s2_tau + c * t0_tau, 2 * gamma)
        sigma_m = (z, h, c)
        return sigma_m, warr

    @staticmethod
    def Verify(pkdS, sigma_m, warr, m, A):
        pk_tau, sigma_tau = warr
        rho, t1_tau = pk_tau
        z, h, c = sigma_m
        w1_p = usehint_polyvec(h, A * z - c * t1_tau * (2^(d_prime - 1)), 2 * gamma)
        if not (infinity_norm_polyvec(z) < gamma - (2 * beta) and c == sample_challenge_hash(m, w1_p, t1_tau)):
            return False
        t1_bytes = encode_dilithium_t1(t1_tau)
        pk_tau_message = base64.b64encode(t1_bytes).decode("utf-8")
        return DilithiumQROM.verify(pkdS, pk_tau_message, sigma_tau)


def test_DPS():
    print("--------------begin----------------")
    m = "".join(random.choices(string.ascii_letters, k=100))
    pkdS, skdS = DPS.dKeyGen()
    print("-----------dKeyGen success---------")
    pk_kem, sk_kem, pkpS, skpS = DPS.pKeyGen()
    print("-----------pKeyGen success---------")
    rho, _, _ = pkpS
    A = sample_matrix_hash(k, l, 0, q - 1, rho)
    ddata, warr = DPS.delegate(pkpS, pk_kem, skdS)
    print("-----------delegate success--------")
    sigma_m, warr = DPS.proxySign(skpS, pkpS, warr, ddata, sk_kem, m)
    print("-----------proxySign success-------")
    res = DPS.Verify(pkdS, sigma_m, warr, m, A)
    assert res is True
    print("-----------Verify success----------")


test_DPS()
print("DONE!")
