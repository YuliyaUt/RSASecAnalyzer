import math
import random
import time


global_timeout = 5*60


def get_param_by_key(params, key, message):
    if (key in params) and (len(params) > (params.index(key) + 1)):
        ind = params.index(key)
        param = params[ind + 1]
    else:
        print(message)
        param = input()
    return param


# Euclid's algorithm
def gcd(a, b):
    if a == 0 or b == 0:
        return 0
    if a < 0:
        a = - a
    if b < 0:
        b = - b
    # s = q * t + r
    s, t = max(a, b), min(a, b)
    r = s % t
    while r != 0:
        s, t = t, r
        r = s % t
    return t


# using Euclid's algorithm
def inverse(a, module):
    a = a % module
    if gcd(a, module) != 1:
        return 0
    n = 1
    s, t = module, a
    q, r = s // t, s % t
    p_prev, p = 0, 1
    while r != 0:
        p_prev, p = p, p * q + p_prev
        s, t = t, r
        q, r = s // t, s % t
        n += 1
    if n % 2 == 0:
        p *= -1
    return p


def continued_fraction_generator(num, den):
    p_n_2, p_n_1 = 0, 1
    q_n_2, q_n_1 = 1, 0
    if den == 0:
        return 0, 0
    a_n = num // den
    p_n = p_n_1 * a_n + p_n_2
    q_n = q_n_1 * a_n + q_n_2
    yield p_n, q_n
    while den != 0:
        num, den = den, num % den
        if den == 0:
            a_n = 0
            continue
        a_n = num // den
        p_n_2, q_n_2 = p_n_1, q_n_1
        p_n_1, q_n_1 = p_n, q_n
        p_n = p_n_1 * a_n + p_n_2
        q_n = q_n_1 * a_n + q_n_2
        yield p_n, q_n
    while True:
        yield p_n, q_n


# Finds square roots. If solution exists in real numbers, it is rounded and returned, otherwise 0, 0
def roots(a, b, c):
    if a == 0:
        if b != 0:
            if c % b == 0:
                return -c//b, -c//b
        return 0, 0
    discriminant = b ** 2 - 4*a*c
    if discriminant <= 0:
        return 0, 0
    discriminant_sqrt_root = math.sqrt(discriminant)
    x1 = (- b + discriminant_sqrt_root) // 2*a
    x2 = (- b - discriminant_sqrt_root) // 2*a
    return int(x1), int(x2)


# Get d from e,p,q params of RSA cryptosystem
def rsa_secret_key_retriever(e, p, q):
    phi_n = (p - 1) * (q - 1)
    d = inverse(e, phi_n) % phi_n
    return d


def load_factor_base():
    base = []
    f = open("primes.txt", "r")
    for i in range(10_000):
        # for i in range(1_000_000):
        j = int(f.readline())
        base.append(j)
    return base


def get_random_prime(primes_filename, length):
    f = open(primes_filename)
    k = f.readline()
    before = 0
    while k and not len(k) == length + 1:
        k = f.readline()
        before += 1
    amount = 0
    while k and len(k) == length + 1:
        amount += 1
        k = f.readline()
    r = random.randint(0, amount)
    f.close()
    f = open(primes_filename)
    for i in range(before + r):
        f.readline()
    k = f.readline()
    if k:
        s = int(f.readline())
    else:
        s = 1
    f.close()
    return s


# Auxiliary function for Pollard's p-1 method
def pollards_m(b):
    m = 1
    length = len(factor_base)
    i = 0
    while i < length:
        p = factor_base[i]
        if p >= b:
            break
        p_k = p
        while p_k < b:
            p_k *= p
        m *= p_k
        i += 1
    return m


def attack_on_rsa_using_pollards_p_minus_1_algorithm(e, n, timeout):
    begin_time = time.time()
    print("Attack using Pollard's (p-1) Algorithm of module", end=" ")
    print("factorization started with params:")
    print("e = ", e, ", N = ", n, ", timeout in seconds = ", timeout, sep="")
    while True:
        now = time.time()
        if now - begin_time > timeout:
            print("Time is out, attack was not successful:(")
            return 0, 0
        # 1 < B < M < sqrt(N), M < B^2
        m, b = 1, 1
        print("Stage one")
        while not (1 < b < m < int(math.sqrt(n)) and m < b * b):
            b = random.randint(2, int(math.sqrt(n)))
            m = random.randint(2, int(math.sqrt(n)))
        print("m =", m, "b =", b)
        print("Counting M(B)")
        m_b = pollards_m(b)
        q = n
        for a_0 in range(2, 10 ** 2):
            now = time.time()
            if now - begin_time > timeout:
                print("Time is out, attack was not successful:(")
                return 0, 0
            # print("A_i=", a_0)
            b_0 = pow(a_0, m_b, n)
            q = math.gcd(b_0 - 1, n)
            if q < n:
                if q > 1:
                    print("SUCCESS")
                break
        if q == 1:
            print("Stage two")
            m_0 = b + 1
            if m_0 % 2 == 0:
                m_0 += 1
            f_m = pow(b_0, m_0 - 1, n) - 1
            g_m = math.gcd(f_m, n)
            while m_0 < m and g_m == 1:
                now = time.time()
                if now - begin_time > timeout:
                    print("Time is out, attack was not successful:(")
                    return 0, 0
                f_m = ((f_m + 1) * (b ** 2) - 1) % n
                g_prev = g_m
                g_m = math.gcd(f_m, n)
                m_0 += 2
            if 1 < g_m < n:
                print(g_m, n // g_m)
                return g_m, n // g_m
            else:
                for k in range(g_prev, g_m):
                    now = time.time()
                    if now - begin_time > timeout:
                        print("Time is out, attack was not successful:(")
                        return 0, 0
                    if 1 < math.gcd(k, n) < n:
                        print(k, n // k)
                        return k, n // k
            break
        elif 1 < q < n:
            print(q, n // q)
            return q, n // q
        else:
            print("Entering new loop cause M,B choice was not successful")


# classic version of algorithm taken from Wikipedia - implemented by me
def pollards_rho_algorithm(n, timeout):
    print("Starting Pollard's rho factorization algorithm", end=" ")
    print("with n =", n)
    s = 100000000
    for x_0 in range(2, 9):
        x_i = x_2i = x_0
        q_i = i = d = 1
        while i <= s and (d in (1, n)):
            x_i = add_mod(x_i * x_i, - 1, n)
            x_2i = add_mod(x_2i * x_2i, - 1, n)
            x_2i = add_mod(x_2i * x_2i, - 1, n)
            q_i = mult_mod(q_i, (x_2i - x_i), n)
            d = gcd(q_i, n)
            i += 1
        if 1 < d < n:
            print("Successful factorization! p =", d, ", q =", n // d)
            return d, n // d
    return 1, n


def attack_on_rsa_using_pollards_rho_method(e, n, timeout):
    print("Attack using Pollard's Rho Algorithm of module", end=" ")
    print("factorization started with params:")
    print("e = ", e, ", N = ", n, ", timeout in seconds = ", timeout, sep="")
    p, q = pollards_rho_algorithm(n, timeout)
    if p not in (1, n):
        d = rsa_secret_key_retriever(e, p, q)
        print("Found d: d = ", d)
    else:
        print("Factorization using Pollard's rho method was not successful")


def remove_zeros_from_end(f):
    size = len(f)
    k = 0
    f.reverse()
    while k < size and f[k] == 0:
        k += 1
    if k == size:
        f = [0]
    else:
        for i in range(k):
            f.remove(0)
    f.reverse()
    return f


def mult_mod(a, b, n):
    return (a * b) % n


def add_mod(a, b, n):
    return (a + b) % n


def poly_div(f, g, n):
    f = remove_zeros_from_end(f)
    g = remove_zeros_from_end(g)
    if f == [0] or g == [0]:
        return [0], [0]
    print(f, g)
    f_size = len(f)
    g_size = len(g)
    q_dict = {}
    for i in range(f_size - g_size + 1):
        coeff = f_size - g_size - i
        val = mult_mod(f[f_size - 1 - i], inverse(g[g_size - 1], n), n)
        q_dict[coeff] = val
        for j in range(g_size):
            f[coeff + j] = add_mod(f[coeff + j], -1 * mult_mod(g[j], val, n), n)
    if not q_dict.keys():
        return [0], [0]
    max_val = max(q_dict.keys())
    q = [q_dict[key] if key in q_dict.keys() else 0 for key in range(max_val + 1)]
    q = remove_zeros_from_end(q)
    r = remove_zeros_from_end(f)
    return q, r


def poly_gcd(f, g, n):
    f = remove_zeros_from_end(f)
    g = remove_zeros_from_end(g)
    if len(g) > len(f):
        f, g = g, f
    # f = g * q + r while r !=0
    q, r = poly_div(f, g, n)
    while r != [0]:
        f, g = g, r
        q, r = poly_div(f, g, n)
    g_size = len(g)
    for i in range(g_size):
        g[i] = mult_mod(g[i], inverse(g[g_size-1], n), n)
    return g


def c_n_k(n, k):
    c = 1
    for i in range(n-k+1, n+1):
        c *= i
    for i in range(1, k+1):
        c //= i
    return c


def ciphertext_recovery_attack_with_chosen_ct(e, n, timeout, a, b, c_1, c_2):
    # fill in the f, g vectors of coefficients of polynoms
    f = [0] * (e + 1)
    g = [0] * (e + 1)
    f[0] = (-c_1) % n
    f[e] = 1
    for i in range(e + 1):
        g[i] = c_n_k(e, i) % n
        g[i] = mult_mod(g[i], pow(a, i, n), n)
        g[i] = mult_mod(g[i], pow(b, e - i, n), n)
    g[0] = add_mod(g[0], - c_2, n)
    print(f, g)
    d = poly_gcd(f, g, n)
    print("d=", d)
    gcd_1 = d
    k = len(d) - 1
    if inverse(k, n):
        recovered_m_1 = mult_mod(- inverse(k, n), d[k - 1], n)
        # check if what we retrieved is really the right message
        for i in range(k):
            gcd_1, j = poly_div(gcd_1, [-recovered_m_1, 1], n)
            if j != [0]:
                pass
        if len(gcd_1) == 1:
            print("Attack successful and recovered m_1 =", recovered_m_1)
    pass


def ciphertext_recovery_attack(e, n, timeout):
    print("Choosing random message")
    # TODO maybe choose a,b randomly?
    a = 2
    b = 1
    m_1 = random.randint(2, n-1)
    m_2 = add_mod(a * m_1, b, n)
    c_1 = pow(m_1, e, n)
    c_2 = pow(m_2, e, n)
    print("Chosen m_1=", m_1)
    ciphertext_recovery_attack_with_chosen_ct(e, n, timeout, a, b, c_1, c_2)


def wieners_attack(e, n, timeout):
    print("Wiener's attack started with params:")
    print("e = ", e, ", N = ", n, ", timeout in seconds = ", timeout, sep="")
    p, q = 1, 1
    generator = continued_fraction_generator(e, n)
    k, d = 1, 1
    while k != e or d != n:
        k, d = next(generator)
        print("kd", k, d)
        if k == 0:
            continue
        if (e*d - 1) % k != 0:
            continue
        phi_n = (e*d - 1) // k
        p, q = roots(1, - (n - phi_n + 1), n)
        print("pq", p, q)
        if p <= 0 or q <= 0:
            continue
        if p * q == n:
            print("Success of Wiener's attack! :) p = ", p, ", q = ", q, sep="")
            break
    if p * q != n:
        print("Wiener's attack was not successful, not applicable :(")
    print(p, q)


def iteration_attack(e, n, timeout):
    print("Iteration attack started with params:")
    print("e = ", e, ", N = ", n, ", timeout in seconds = ", timeout, sep="")
    found = False
    p, q = 1, n
    while not found:
        m = random.randint(2, 2**8)
        if n == m:
            continue
        if gcd(n, m) > 1:
            p, q = m, n // m
        c = pow(m, e, n)
        i = 2
        c_i = pow(c, e, n)
        while gcd(c_i-c, n) == 1:
            i += 1
            c_i = pow(c_i, e, n)
        if gcd(c_i-c, n) == n:
            print("Unlucky number", m)
            continue
        p, q = gcd(c_i - c, n), n // gcd(c_i - c, n)
        found = True
        print("Found! Iterations number:", i)
    if p not in (1, n):
        d = rsa_secret_key_retriever(e, p, q)
        print("Found d: d = ", d)
        print(p, q)
    else:
        print("Factorization using iteration attack method was not successful")


def test_mode(params):
    timeout_param = global_timeout
    # TODO: write normal test mode
    wieners_attack(1061933, 1329827, timeout_param)
    wieners_attack(inverse(13, 59440 * 67452), 59441 * 67453, timeout_param)
    wieners_attack(inverse(13, 345230142 * 815047702), 345230143 * 815047703, timeout_param)
    wieners_attack(inverse(13, 477224802150430 * 639414754117956), 477224802150431 * 639414754117957, timeout_param)
    attack_on_rsa_using_pollards_rho_method(13, 59441 * 67453, timeout_param)
    attack_on_rsa_using_pollards_rho_method(11, 345230143 * 815047703, timeout_param)
    # attack_on_rsa_using_pollards_rho_method(11, 477224802150431 * 639414754117957, timeout_param) #Too long
    iteration_attack(11, 2319201790063859, timeout_param)
    iteration_attack(13, 345230143 * 815047703, timeout_param)
    # iteration_attack(11, 477224802150431 * 639414754117957, timeout_param)
    # assert d = 1475855606789531
    attack_on_rsa_using_pollards_p_minus_1_algorithm(11, 10001, timeout_param)
    attack_on_rsa_using_pollards_p_minus_1_algorithm(11, 59441 * 67453, timeout_param)
    # attack_on_rsa_using_pollards_p_minus_1_algorithm(11, 345230143 * 815047703, timeout_param)
    # attack_on_rsa_using_pollards_p_minus_1_algorithm(11, 477224802150431 * 639414754117957, timeout_param) #Too long
    ciphertext_recovery_attack_with_chosen_ct(4, 697, 1, 2, 1, 86, 633)
    pass


def analysis_mode(params):
    timeout_param = int(get_param_by_key(params, "-t", "Enter timeout for one attack (in seconds)"))
    e_param = int(get_param_by_key(params, "-e", "Enter e of public key"))
    n_param = int(get_param_by_key(params, "-n", "Enter N of public key"))
    attack_on_rsa_using_pollards_p_minus_1_algorithm(e_param, n_param, timeout_param)
    attack_on_rsa_using_pollards_rho_method(e_param, n_param, timeout_param)
    ciphertext_recovery_attack(e_param, n_param, timeout_param)
    wieners_attack(e_param, n_param, timeout_param)
    iteration_attack(e_param, n_param, timeout_param)
    return 0


def main ():
    print("-------------------------RSA Security Analyzer-------------------------")
    print("Enter '/test [-n system_parameter] [-a attacks list]' for test mode")
    print("Enter '/analyze [-e e] [-n N] [-t timeout_in_seconds]' for public key security analysis")
    command = input()
    if not command:
        return 0
    params = command.split(" ")
    mode = params[0]
    if mode == "/test":
        test_mode(params)
    elif mode == "/analyze":
        analysis_mode(params)
    else:
        print("Couldn't recognize a command")


factor_base = load_factor_base()

# TODO: introduce timeouts
# TODO: introduce reports
if __name__ == "__main__":
    main()
