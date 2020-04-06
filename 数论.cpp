#include <cstdio>
#include <iostream>
#include <cmath>
typedef long long ll;
const int inf = 0x3f3f3f3f, N = 100010, mod = 998244353;

namespace _gcd {
    ll gcd(ll a, ll b) {
        if(!b) return a;
        return gcd(b, a % b);
    }
}

namespace _lcm {
    using namespace _gcd;
    ll lcm(ll a, ll b) {
        return a / gcd(a, b) * b;
    }
}

namespace _exgcd {
    void exgcd(ll a, ll b, ll & x, ll & y) {
        if(!b) x = 1, y = 0;
        else exgcd(b, a % b, y, x), y -= a / b * x;
    }
}

namespace _qmul {
    ll qmul(ll a, ll b, ll mod) { // O(logN)
        ll ret = 0;
        while(b) {
            if(b & 1) ret = (ret + a) % mod;
            a = (a + a) % mod;
            b >>= 1;
        } return ret;
    }
    ll mul(ll a, ll b, ll mod) { // O(1)
        ll ans = a * b - (ll)((long double) a * b / mod + 0.1) * mod;
        return ans < 0 ? ans + mod : ans;
    }
}

namespace _qpow {
    using namespace _qmul;
    int qpow(int a, int b) {
        int ret = 1;
        while(b) {
            if(b & 1) ret = 1ll * ret * a % mod;
            a = 1ll * a * a % mod;
            b >>= 1;
        } return ret;
    }
    ll qpow(ll a, ll b, ll mod) {
        ll ans = 1;
        while(b) {
            if(b & 1) ans = mul(ans, a, mod);
            a = mul(a, a, mod);
            b >>= 1;
        } return ans;   
    }
}

namespace _Miller_Rabin { // 判断素数
    using namespace _qpow;
    ll prim[10] = {2, 3, 5, 7, 11, 13, 17, 19, 23};
    bool Miller_Rabin(ll n) {
        if(n == 2) return true;
        if(n < 2 || n % 2 == 0) return false;
        ll d = n - 1, s = 0;
        while(d % 2 == 0) d >>= 1, ++s;
        for(int i = 0; i < 9; ++i) {
            ll p = prim[i], w = qpow(p, d, n);
            if(w == 1 || w == n - 1 || p == n) continue;
            for(int j = 1; j <= s; ++j) {
                ll u = mul(w, w, n);
                if(u == 1 && w != 1 && w != n - 1) return false;
                w = u;
            }
            if(w != 1) return false;
        }
        return true;
    }
}

namespace _Pollard_Tho { // 找一个因数
    using namespace _Miller_Rabin;
    using namespace _gcd;
    ll Pollard_Tho(ll n, ll c) {
        ll x = rand() % n, y = x, p = 1;
        for(int step = 1; ; step <<= 1, y = x, p = 1) {
            for(int i = 1; i <= step; ++i) {
                x = (mul(x, x, n) + c) % n;
                p = mul(p, abs(x - y), n);
                if(i % 127 == 0) {
                    ll d = gcd(p, n);
                    if(d > 1) return d;
                }
            }
            ll d = gcd(p, n);
            if(d > 1) return d;
        }
    }
    ll ans;
    void solve(ll n) {
        if(n <= ans) return;
        if(n == 1) return;
        if(Miller_Rabin(n)) {ans = n; return;}
        ll t = n;
        while(t == n) t = Pollard_Tho(n, rand() % (n - 1) + 1);
        solve(t); solve(n / t);
    }
}

namespace _euler {
    int euler(int x) { // 求欧拉函数，质因数分解，每次乘 (p - 1) / p
        int m = sqrt(x + 0.5);
        int ans = x;
        for(int i = 2; i <= m; ++i)
            if(x % i == 0) {
                ans = ans / i * (i - 1);
                while(x % i == 0) x /= i;
            }
        if(x > 1) ans = ans / x * (x - 1);
        return ans;
    }
}

namespace _expEuler {
    using namespace _euler;
    using namespace _qpow;
    // a ^ b % m , b = 10^20000
    int a, b, m, pm;
    void getb() {
        int f = 0;
        // 快读
        if(b > pm) b %= pm, f = 1; // 边读入边取模
        // 快读结束
        if(f) b += pm;
    }
    void solve() {
        pm = euler(m);
        getb();
        qpow(a, b, m);
    }
}

namespace _shai { // 筛法
    int prim[N], vis[N], pc;
    void getPrim(int n) { // 质数
        vis[1] = 1;
        for(int i = 2; i <= n; ++i) {
            if(!vis[i]) prim[++pc] = i;
            for(int j = 1; j <= pc; ++j) {
                if(i * prim[j] > n) break;
                vis[i * prim[j]] = 1;
                if(i % prim[j] == 0) break; // 只用最小的因数
            }
        }
    }
    int phi[N];
    void getPhi(int n) { // 欧拉函数
        vis[1] = 1;
        for(int i = 2; i <= n; ++i) {
            if(!vis[i]) prim[++pc] = i;
            for(int j = 1; j <= pc; ++j) {
                if(i * prim[j] > n) break;
                vis[i * prim[j]] = 1;
                if(i % prim[j] == 0) { phi[i * prim[j]] = phi[i] * prim[j]; break; }
                else phi[i * prim[j]] = phi[i] * (prim[j] - 1);
            }
        }
    }
    int mu[N];
    void getMu(int n) { // 莫比乌斯函数 和 质数
        mu[1] = 1; vis[1] = 1;
        for(int i = 2; i <= n; ++i) {
            if(!vis[i]) mu[i] = -1, prim[++pc] = i;
            for(int j = 1; j <= pc; ++j) {
                if(i * prim[j] > n) break;
                vis[i * prim[j]] = 1;
                if(i % prim[j] == 0) break;
                else mu[prim[j] * i] = -mu[i];
            }
        }
    }
    void getAll(int n) {
        mu[1] = 1; vis[1] = 1;
        for(int i = 2; i <= n; ++i) {
            if(!vis[i]) mu[i] = -1, prim[++pc] = i;
            for(int j = 1; j <= pc; ++j) {
                if(i * prim[j] > n) break;
                vis[i * prim[j]] = 1;
                if(i % prim[j] == 0) { phi[i * prim[j]] = phi[i] * prim[j]; break; }
                else phi[i * prim[j]] = phi[i] * (prim[j] - 1), mu[prim[j] * i] = -mu[i];
            }
        }
    }
}

namespace _inv {
    using namespace _qpow;
    using namespace _exgcd;
    int inv1(int a, int mod) { return qpow(a, mod - 2); } // 费马小定理
    int inv2(int a, int mod) { // 扩欧 
        int x = 0, y = 0;
        exgcd(a, mod, x, y);
        return (x % mod + mod) % mod;
    }
    int inv[N];
    void getInv(int n, int mod) { // 线性求逆元
        inv[1] = 1;
        for(int i = 2; i < n; ++i) 
            inv[i] = 1ll * (mod - mod / i) * inv[mod % i] % mod; 
    }
    int sv[N], s[N];
    void getInv2(int n, int mod, int * a) { // 任意n个数的逆元
        s[0] = 1; // 前缀积
        for(int i = 1; i <= n; ++i) s[i] = s[i - 1] * a[i] % mod;
        sv[n] = qpow(s[n], mod - 2); // 积的逆元
        for(int i = n; i >= 1; --i) sv[i - 1] = sv[i] * a[i] % mod;
        for(int i = 1; i <= n; ++i) inv[i] = sv[i] * s[i - 1] % mod;
    }
    int fac[N];
    void getFacInv(int n, int mod) {
        fac[0] = 1;
        for(int i = 1; i <= n; ++i) fac[i] = fac[i - 1] * i % mod;
        inv[n] = qpow(fac[n], mod - 2);
        for(int i = n - 1; i >= 0; --i) inv[i] = inv[i + 1] * (i + 1) % mod;
    }
}

namespace _crt {
    using namespace _inv;
    int a[N], n, mod[N];
    int crt() {
        ll M = 1; int ans = 0;
        for(int i = 1; i <= n; ++i) M *= mod[i];
        for(int i = 1; i <= n; ++i) {
            ll mi = M / mod[i];
            ll ci = 1ll * mi * inv1(mi, mod[i]) % M;
            ans = (ans + 1ll * a[i] * mi % M * ci % M) % M;
        }
        return ans;
    }
}

namespace _excrt {
    using namespace _exgcd;
    using namespace _gcd;
    using namespace _qmul;
    int m[N], a[N], n;
    ll excrt() { // 两两求解
        ll M = m[1], x = a[1], p, q;
        for(int i = 2; i <= n; ++i) {
            exgcd(M, m[i], p, q);
            ll d = gcd(M, m[i]), c = (a[i] - x + m[i]) % m[i];
            if(c % d != 0) return -1;
            x = mul(x, c / d, m[i] / d);
            
        }
    }
}