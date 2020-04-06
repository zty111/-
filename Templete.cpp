#include <cstdio>
#include <iostream>
#include <cstring>
#include <queue>
#include <cstdlib>
#include <complex>
#include <cmath>
using namespace std;
typedef long long ll;
typedef unsigned long long ull;
const int N = 1e6, mod = 998244353, inf = 0x3f3f3f3f;

/* README
`this cpp is used for reviewing Templetes.
`Here is an example:
namespace _TempleteName {
    int; // data struct
    Name() {
        ...
    } // main body
    int main() { Name(); } // how to be used
}
*/

namespace _dsu {
    int f[N], siz[N], n;
    int find(int x) {
        if(f[x] == x) return x;
        else return f[x] = find(f[x]); //路径压缩
    }
    void merge(int x, int y) {
        int fx = find(x), fy = find(y);
        if(fx == fy) return;
        if(siz[fx] < siz[fy]) swap(fx, fy);
        f[fy] = fx; siz[fx] += siz[fy]; 
    } //按秩合并 把y合并到x上
    void init() {
        for(int i = 1; i <= n; ++i) f[i] = i, siz[i] = 1;
    }
}

namespace _gcd {
    ll gcd(ll a, ll b) {
        if(!b) return a;
        return gcd(b, a % b);
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

namespace _stack {
    int s[N], top;
    void insert(int a) {
        while(s[top] < a) --top;
        s[++top] = a;
    }
} // 单调栈

namespace _trie {
    const int b = 'a', siz = 26;
    int ch[N][siz], cnt, num[N];
    void insert(char * s) {
        int now = 0;
        for(; *s; s++) {
            if(!ch[now][*s - b]) ch[now][*s - b] = ++cnt;
            now = ch[now][*s - b];
        }
        ++num[now];
    }
    int find(char * s) {
        int now = 0;
        for(; *s; ++s) {
            if(!ch[now][*s - b]) return 0;
            now = ch[now][*s - b];
        }
        return num[now];
    }
}

namespace _AC {
    using namespace _trie;
    int fail[N];
    void buildAC() {
        queue<int> q;
        for(int i = 0; i < siz; ++i)
            if(ch[0][i]) q.push(ch[0][i]);
        while(q.size()) {
            int u = q.front(); q.pop();
            for(int i = 0; i < siz; ++i)
                if(ch[u][i]) fail[ch[u][i]] = ch[fail[u]][i], q.push(ch[u][i]);
                else ch[u][i] = ch[fail[u]][i];
        }
    }
    void query(char * s) {
        int now = 0, ans = 0;
        for(; *s; ++s) {
            now = ch[now][*s - b];
            for(int t = now; t && num[t]; t = fail[t]) ans += num[t], num[t] = 0;
        }
    }
}

namespace _SAT {
    int vis[N << 2], s[N << 1], top, n;
    vector<int> G[N];
    bool dfs(int x) {
        if(vis[x ^ 1]) return false;
        if(vis[x]) return true;
        vis[x] = 1;
        s[++top] = x;
        for(int i = 0; i < G[x].size(); ++i)
            if(!dfs(G[x][i])) return false;
        return true;
    }
    bool solve() {
        for(int i = 2; i <= (n << 1); ++i)
            if(!vis[i] && !vis[i + 1]) {
                top = 0;
                if(!dfs(i)) {
                    while(top) vis[s[top--]] = 0;
                    if(!dfs(i + 1)) return false;
                }
            }
        return true;
    }
    void add_clause(int x, int xval, int y, int yval) {
        x = (x << 1) + xval;
        y = (y << 1) + yval;
        G[x ^ 1].push_back(y);
        G[y ^ 1].push_back(x);
    }
}

namespace _SAM {
    int len[N], nxt[N][26], link[N], cnt, last;
    char s[N];
    void init() {
        cnt = last = 1;
        memset(link, 0, sizeof(link));
    }
    void extend(int c) {
        int cur = ++cnt, p = last;
        len[cur] = len[p] + 1;
        while(p && !nxt[p][c]) {
            nxt[p][c] = cur; p = link[p];
        }
        if(!p) link[cur] = 1;
        else {
            int q = nxt[p][c];
            if(len[q] == len[p] + 1) link[cur] = q;
            else {
                int clone = ++cnt;
                for(int i = 0; i < 26; ++i) nxt[clone][i] = nxt[q][i];
                link[clone] = link[q];
                len[clone] = len[p] + 1;
                while(p && nxt[p][c] == q) {
                    nxt[p][c] = clone; p = link[p];
                }
                link[q] = link[cur] = clone;
            }
        }
        last = cur;
    }
    void add(int a, int b);
    int main() {
        int m = strlen(s); init();
        for(int i = 0; i < m; ++i) extend(s[i] - 'a');
        for(int i = 2; i <= cnt; ++i) add(i, link[i]);
        return 0;
    }
}

namespace _FWT {
    int n, a[N], b[N], c[N], inv2, mod;
    void FWT(int * a, int op, char c) {
        for(int i = 1; i < n; i <<= 1) {
            int i2 = i << 1;
            for(int j = 0; j < n; j += i2)
                for(int k = 0; k < i; ++k)
                    if(c == '&') a[i + j + k] += 1ll * a[j + k] * op % mod, a[i + j + k] %= mod;
                    else if(c == '|') a[j + k] += 1ll * a[i + j + k] * op % mod, a[j + k] %= mod;
                    else if(c == '^') {
                        a[j + k] = (a[j + k] + a[i + j + k]) % mod;
                        a[i + j + k] = (a[j + k] - a[i + j + k] * 2 % mod + mod) % mod;
                        a[j + k] = 1ll * a[j + k] * op % mod;
                        a[i + j + k] = 1ll * a[i + j + k] * op % mod;
                    }
        }
    }
    int main() {
        FWT(a, 1, '&'); FWT(b, 1, '&');
        for(int i = 1; i < n; ++i) c[i] = 1ll * a[i] * b[i] % mod;
        FWT(c, '^' ? inv2 : mod - 1, '&');
        return 0;
    }
}

namespace _FFT {
    const double PI = 3.1415926;
    typedef complex<double> cd;
    int pos[N], n, m, num;
    cd a[N], b[N];
    void FFT(cd * a, int len, int op) {
        for(int i = 0; i < len; ++i) if(i < pos[i]) swap(a[i], a[pos[i]]);
        for(int i = 1; i < len; i <<= 1) {
            int step = i << 1;
            cd wn = cd(cos(PI/i), op * sin(PI/i));
            for(int j = 0; j < len; j += step) {
                cd w = cd(1, 0);
                for(int k = 0; k < i; ++k, w = w * wn) {
                    cd x = a[k + j];
                    cd y = w * a[k + j + i];
                    a[k + j] = x + y;
                    a[k + j + i] = x - y;
                }
            }
        }
        if(op == -1) for(int i = 0; i < len; ++i) a[i] = cd(a[i].real() / len + 0.5, 0);
    }
    int main() {
        int len = n + m;
        while(len) len >>= 1, ++num;
        len = 1 << num;
        for(int i = 0; i < len; ++i) pos[i] = (pos[i>>1]>>1) | ((i & 1) << (num - 1));
        FFT(a, len, 1); FFT(b, len, 1);
        for(int i = 0; i < len; ++i) a[i] = a[i] * b[i];
        FFT(a, len, -1);
        for(int i = 0; i < m + n + 1; ++i) printf("%d ", (int(a[i].real())));
        return 0;
    }
}

namespace _NTT {
    using namespace _qpow;
    const int gi = 3; // k * 2 ^ n(足够大) + 1
    int pos[N], a[N], b[N], c[N], n, m, num;
    void pre(int len) {
        for(int i = 0; i < len; ++i) pos[i] = (pos[i>>1]>>1) | ((i & 1) <<num);
    }
    void NTT(int * a, int len, int op) {
        for(int i = 0; i < len; ++i) if(i < pos[i]) swap(a[i], a[pos[i]]);
        for(int i = 1; i < len; i <<= 1) {
            int step = i << 1;
            int g0 = qpow(gi, (mod - 1) / step);
            if(op == -1) g0 = qpow(g0, mod - 2);
            for(int j = 0; j < len; j += step) {
                int gnow = 1;
                for(int k = 0; k < i; ++k, gnow = 1ll * gnow * g0 % mod) {
                    int x = a[k + j];
                    int y= 1ll * gnow * a[k + j + i] % mod;
                    a[k + j] = (x + y) % mod;
                    a[i + k + j] = (x - y + mod) % mod;
                }
            }
        }
        if(op == -1) {
            int inv = qpow(len, mod -2);
            for(int i = 0; i < len; ++i) a[i] = 1ll * a[i] * inv % mod;
        }
    }
    int main() {
        int len = n + m;
        while(len) len >>= 1, ++num;
        len = 1 << num;
        for(int i = 0; i < len; ++i) pos[i] = (pos[i>>1]>>1) | ((i & 1) << (num - 1));
        NTT(a, len, 1); NTT(b, len, 1);
        for(int i = 0; i < len; ++i) c[i] = 1ll * a[i] * b[i] %  mod;
        NTT(c, len, -1);
        for(int i = 0; i < n + m + 1; ++i) printf("%d ", c[i]);
        return 0;
    }
}

namespace _NTT_all {
    const int mod[3] = {998244353, 1004535809, 469762049}, gi = 3;
    int f[3][N], g[3][N], h[3][N], p, n, m, num, pos[N];
    ll ans[N];
    int qpow(int a, int b, int i) {
        int c = 1; a %= mod[i];
        while(b) {
            if(b & 1) c = 1ll * c * a % mod[i];
            a = 1ll * a * a % mod[i];
            b >>= 1;
        } return c;
    }
    void NTT(int * a, int len, int op, int b) {
        for(int i = 0; i < len; ++i) if(i < pos[i]) swap(a[i], a[pos[i]]);
        for(int i = 1; i < len; i <<= 1) {
            int step = i << 1;
            int g0 = qpow(gi, (mod[b] - 1) / step, b);
            if(op == -1) g0 = qpow(g0, mod[b] - 2, b);
            for(int j = 0; j < len; j += step) {
                int gnow = 1;
                for(int k = 0; k < i; ++k, gnow = 1ll * gnow * g0 % mod[b]) {
                    int x = a[k + j];
                    int y = 1ll * gnow * a[k + j + i] % mod[b];
                    a[k + j] = (x + y) % mod[b];
                    a[k + j + i] = (x - y + mod[b]) % mod[b];
                }
            }
        }
        if(op == -1) {
            int inv = qpow(len, mod[b] - 2, b);
            for(int i = 0; i < len; ++i) a[i] = 1ll * a[i] * inv % mod[b];
        }
    }
    ll qmul(ll a, ll b, ll mod) {
        ll ans = (a * b - (ll) ((long double) a / mod * b + 0.1) * mod) % mod;
        return ans < 0 ? ans + mod : ans;
    }
    void CRT(int len) {
        ll M = 1ll * mod[0] * mod[1];
        ll c1 = qpow(mod[1], mod[0] - 2, 0);
        ll c2 = qpow(mod[0], mod[1] - 2, 1);
        ll inv = qpow(M % mod[2], mod[2] - 2, 2);
        for(int i = 0; i < len; ++i) {
            ll A = (qmul(1ll * h[0][i] * mod[1] % M, c1, M) + qmul(1ll * h[1][i] * mod[0] % M, c2, M)) % M;
            ll k = ((h[2][i] - A) % mod[2] + mod[2]) % mod[2] * inv % mod[2];
            ans[i] = (k % p * (M % p) % p + A % p) % p;
        }
    }
    int main() {
        int len = n + m;
        while(len) len >>= 1, ++num;
        len = 1 << num;
        for(int i = 0; i < len; ++i) pos[i] = (pos[i>>1]>>1) | ((i & 1) << (num - 1));
        for(int i = 0; i < 3; ++i) {
            NTT(&f[i][0], len, 1, i); NTT(&g[i][0], len, 1, i);
            for(int j = 0; j < len; ++j) h[i][j] = 1ll * f[i][j] * g[i][j] % mod[i];
            NTT(&h[i][0], len, -1, i);
        }
        CRT(len);
        for(int i = 0; i < n + m + 1; ++i) printf("%lld ", ans[i]);
        return 0;
    }
}

namespace _polyinv {
    using namespace _NTT;
    void polyinv(int * a, int * b, int len) { // len为2的倍数
        static int t[N];
        for(int i = 0; i < 2 * len; ++i) b[i] = 0;
        b[0] = qpow(a[0], mod - 2);
        for(int i = 2, num = 1; i <= len; i <<= 1, ++num) {
            int i2 = i << 1;
            for(int j = 0; j < i; ++j) t[j] = a[j];
            for(int j = i; j < i2; ++j) t[j] = 0;
            pre(i2);
            NTT(b, i2, 1); NTT(t, i2, 1);
            for(int j = 0; j < i2; ++j) b[j] = 1ll * b[j] * (2 - 1ll * b[j] * t[j] % mod + mod) % mod;
            NTT(b, i2, -1);
            for(int j = i; j < i2; ++j) b[j] = 0;
        }
    }
}

namespace _polysqrt {
    using namespace _polyinv;
    const int inv2 = qpow(2, mod - 2);
    void polysqrt(int * a, int * b, int len) { // len为2的倍数
        static int t[N], t2[N];
        for(int i = 0; i < len * 2; ++i) b[i] = 0;
        b[0] = 1;
        for(int i = 2, num = 1; i <= len; i <<= 1, ++num) {
            int i2 = i << 1;
            for(int j = 0; j < i; ++j) t[j] = a[j];
            for(int j = i; j < i2; ++j) t[j] = 0;
            polyinv(b, t2, i);
            pre(i2);
            NTT(t, i2, 1); NTT(t2, i2, 1); NTT(b, i2, 1);
            for(int j = 0; j < i2; ++j) t[j] = 1ll * t[j] * t2[j] % mod, b[j] = 1ll * (b[j] + t[j]) * inv2 % mod;
            NTT(b, i2, -1);
            for(int j = i; j < i2; ++j) b[j] = 0;
        }
    }
}

namespace _polydiv {
    using namespace _polyinv;
    void polydiv(int * a, int * b, int * c, int * d, int n, int m) { // a / b = c; a % b = d;
        static int t1[N], t2[N];
        int len = 1, l = n - m + 1, num = 0;
        while(len < (l << 1)) len <<= 1, ++num;
        for(int i = 0; i < m; ++i) t1[i] = b[m - i - 1];
        for(int i = l; i < len; ++i) t1[i] = 0;
        polyinv(t1, t2, len);
        for(int i = l; i < len; ++i) t2[i] = 0;
        pre(len);
        NTT(t2, len, 1);
        for(int i = 0; i < n; ++i) t1[i] = a[n - i - 1];
        for(int i = l; i < len; ++i) t1[i] = 0;
        NTT(t1, len, 1);
        for(int i = 0; i < len; ++i) t1[i] = 1ll * t1[i] * t2[i] % mod;
        NTT(t1, len, -1);
        for(int i = 0; i < l - i - 1; ++i) swap(t1[i], t1[l - i - 1]);
        for(int i = 0; i < l; ++i) c[i] = t1[i];
        len = 1; num = 0;
        while(len < n) len <<= 1, ++num;
        for(int i = l; i < len; ++i) t1[i] = 0;
        pre(len);
        NTT(t1, len, 1);
        for(int i = 0; i < m; ++i) t2[i] = b[i];
        for(int i = m; i < len; ++i) t2[i] = 0;
        NTT(t2, len, 1);
        for(int i = 0; i < len; ++i) t1[i] = 1ll * t1[i] * t2[i] % mod;
        NTT(t1, len, -1);
        for(int i = 0; i < m - 1; ++i) d[i] = ((a[i] - t1[i]) % mod + mod) % mod;
    }
}


namespace _polyln {
    using namespace _polyinv;
    void direv(int * a, int * b, int len) {
        for(int i = 1; i < len; ++i) b[i - 1] = 1ll * i * a[i] % mod;
        b[len - 1] = 0;
    }
    void inter(int * a, int * b, int len) {
        b[0] = 0;
        for(int i = 1; i < len; ++i) b[i] = 1ll * a[i - 1] * qpow(i, mod - 2) % mod;
    }
    void polyln(int * a, int * b, int n) {
        static int t1[N], t2[N];
        int len = 1, num = 0; while(len < n) len <<= 1, ++num;
        direv(a, t1, len); polyinv(a, t2, len);
        len <<= 1; ++num; pre(len);
        NTT(t1, len, 1); NTT(t2, len, 1);
        for(int i = 0; i < len; ++i) t1[i] = 1ll * t1[i] * t2[i] % mod;
        NTT(t1, len, -1);
        inter(t1, b, len >> 1);
    }
}

namespace _cdqNTT {
    using namespace _NTT;
    int t1[N], t2[N], g[N], f[N];
    void cdqNTT(int l, int r) { // [l, r)
        if(l + 1 >= r) return;
        int mid = (l + r) >> 1;
        cdqNTT(l, mid);
        int len = r - len; pre(len);
        for(int i = 0; i < len; ++i) t1[i] = g[i];
        for(int i = l; i < mid; ++i) t2[i - l] = f[i];
        for(int i = mid; i < r; ++i) t2[i - l] = 0;
        NTT(t2, len, 1); NTT(t1, len, 1);
        for(int i = 0; i < len; ++i) t1[i] = 1ll * t1[i] * t2[i] % mod;
        NTT(t1, len, -1);
        for(int i = mid; i < r; ++i) f[i] = (f[i] + t1[i - l]) % mod;
        cdqNTT(mid, r);
    }
    int main() {
        int len = 0;
        f[0] = 1;
        cdqNTT(0, len); // len为2的倍数
        return 0;
    }
}

namespace polyexp {
    using namespace _NTT;
    int t1[N], t2[N], g[N], f[N];
    void cdqNTT(int l, int r) { //[l,r)
        if(l + 1 == r) {
            if(l) f[l] = 1ll * f[l] * qpow(l, mod - 2) % mod;
            return;
        }
        int mid = (l + r) >> 1;
        cdqNTT(l, mid);
        int len = r - l; pre(len);
        for(int i = 0; i < len; ++i) t1[i] = g[i];
        for(int i = l; i < mid; ++i) t2[i - l] = f[i];
        for(int i = mid; i < r; ++i) t2[i - l] = 0;
        NTT(t2, len, 1); NTT(t1, len, 1);
        for(int i = 0; i < len; ++i) t1[i] = 1ll * t1[i] * t2[i] % mod;
        NTT(t1, len, -1);
        for(int i = mid; i < r; ++i) f[i] = (f[i] + t1[i - l - 1]) % mod;
        cdqNTT(mid, r);
    }
    int main() {
        scanf("%d", &n);
        for(int i = 0; i < n; ++i) scanf("%d", &g[i]);
        int len = 1; while(len < n) len <<= 1;
        for(int i = 1; i < len; ++i) g[i - 1] = 1ll * i * g[i] % mod; g[len - 1] = 0;
        f[0] = 1; // ***
        cdqNTT(0, len);
        for(int i = 0; i < n; ++i) printf("%d ", f[i]);
        return 0;
    }
}

namespace LCT {
    #define V void 
    #define I int
    #define C char
    #define B bool
    #define lc c[x][0]
    #define rc c[x][1]
    const int N = 300010;
    I n, m, v[N], c[N][2], f[N], s[N], st[N], r[N];
    // Splay
    inline B nR(I x) {return c[f[x]][0] == x || c[f[x]][1] == x;}
    V pU(I x) {s[x] = s[lc] ^ s[rc] ^ v[x];}
    V pR(I x) {
        I t = lc; lc = rc; rc = t;
        r[x] ^= 1;
    }
    V pD(I x) {
        if(r[x]) {
            if(lc) pR(lc); if(rc) pR(rc);
            r[x] = 0;
        }
    }
    V rotate(I x) {
        I y = f[x], z = f[y], k = c[y][1] == x, w = c[x][!k];
        if(nR(y)) c[z][c[z][1] == y] = x;
        c[x][!k] = y; c[y][k] = w;
        if(w) f[w] = y;
        f[y] = x; f[x] = z;
        pU(y);
    }
    V splay(I x) {
        I y = x, z = 0;
        st[++z] = y;
        while(nR(y)) st[++z] = y = f[y];
        while(z) pD(st[z--]);
        while(nR(x)) {
            y = f[x]; z = f[y];
            if(nR(y)) rotate((c[y][0] == x) ^ (c[z][0] == y) ? x : y);
            rotate(x);
        }
        pU(x);
    }
    // LCT
    V access(I x) {
        for(I y = 0; x; x = f[y = x])
            splay(x), rc = y, pU(x);
    }
    V mR(I x) {
        access(x); splay(x); pR(x);
    }
    I fR(I x) {
        access(x); splay(x);
        while(lc) pD(x), x = lc;
        splay(x);
        return x;
    }
    V split(I x, I y) {
        mR(x); access(y); splay(y);
    }
    V link(I x, I y) {
        mR(x); if(fR(y) != x) f[x] = y;
    }
    V cut(I x, I y) {
        mR(x);
        if(fR(y) == x && f[y] == x && !c[y][0])
            f[y] = c[x][1] = 0, pU(x);
    }
}

namespace _zkwflow {
    int n, m, pi1, cost, h[N], v[N], up[N], to[N], nxt[N], c[N], cnt = 1, s, t, maxflow;
    int aug(int u, int m) {
        if(u == t) {
            cost += pi1 * m;
            maxflow += m;
            return m;
        }
        v[u] = true;
        int l = m;
        for(int i = h[u]; i; i = nxt[i])
            if(up[i] && !c[i] && !v[to[i]]) {
                int d = aug(to[i], l < up[i] ? l : up[i]);
                up[i] -= d; up[i^1] += d; l -= d;
                if(!l) return m;
            }
        return m - l;
    }
    bool modlabel() {
        int d = inf;
        for(int i = 1; i <= n; ++i) if(v[i])
            for(int j = h[i]; j; j = nxt[j])
                if(up[j] && !v[to[j]] && c[j] < d) d = c[j];
        if(d == inf) return false;
        for(int i = 1; i <= n; ++i) if(v[i])
            for(int j = h[i]; j; j = nxt[j])
                c[j] -= d, c[j^1] += d;
        pi1 += d;
        return true;
    }
    void add_edge(int u, int v, int cap, int cost) {
        ++cnt; nxt[cnt] = h[u]; to[cnt] = v; up[cnt] = cap; c[cnt] = cost; h[u] = cnt; 
    }
    void zkw() {
        do 
            do memset(v, 0, sizeof(v)); 
            while(aug(s, inf));
        while(modlabel());
    }
}

namespace _Miller_Rabin {
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

namespace _Pollard_Tho {
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

namespace _PAM {
    char s[N];
    struct node {
        int sum, len;
        int fail;
        int ch[26];
    }p[N];
    int cnt, la;
    void insert(int i) {
        int cur = la;
        while(s[i - p[cur].len - 1] != s[i]) cur = p[cur].fail;
        if(!p[cur].ch[s[i] - 'a']) {
            p[++cnt].len = p[cur].len + 2;
            int fa = p[cur].fail;
            while(s[i - p[fa].len - 1] != s[i]) fa = p[fa].fail;
            fa = p[fa].ch[s[i] - 'a'];
            p[cnt].fail = fa;
            p[cnt].sum = p[fa].sum + 1;
            p[cur].ch[s[i] - 'a'] = cnt;
        }
        la = p[cur].ch[s[i] - 'a'];
    }
    int main() {
        scanf("%s", s+1);
        int len = strlen(s+1);
        p[0].fail = 1; p[1].len = -1;
        cnt = 1;
        for(int i = 1; i <= len; ++i) {
            s[i] = (s[i] - 97 + p[la].sum) % 26 + 97;
            insert(i);
            printf("%d ", p[la].sum);
        }
        return 0;
    }
}

namespace _SA {
    char s[N];
    int n, w, sa[N], rk[N<<1], oldrk[N<<1], id[N], px[N], cnt[N];
    bool cmp(int a, int b, int w) {
        return oldrk[a] == oldrk[b] && oldrk[a+w] == oldrk[b+w];
    }
    int main() {
        scanf("%s", s+1);
        n = strlen(s+1);
        int m = 150, i, p, w;
        for(i = 1; i <= n; ++i) ++cnt[rk[i] = s[i]];
        for(i = 1; i <= m; ++i) cnt[i] += cnt[i-1];
        for(i = n; i >= 1; --i) sa[cnt[rk[i]]--] = i;
    
        for(w = 1; w < n; w <<= 1, m = p) {
            for(p = 0, i = n; i > n - w; --i) id[++p] = i;
            for(i = 1; i <= n; ++i)
                if(sa[i] > w) id[++p] = sa[i] - w;
            for(i = 1; i <= m; ++i) cnt[i] = 0;
            for(i = 1; i <= n; ++i) ++cnt[px[i] = rk[id[i]]];
            for(i = 1; i <= m; ++i) cnt[i] += cnt[i-1];
            for(i = n; i >= 1; --i) sa[cnt[px[i]]--] = id[i];
            swap(rk, oldrk);
            for(p = 0, i = 1; i <= n; ++i)
                rk[sa[i]] = cmp(sa[i], sa[i-1], w) ? p : ++p;
        }
        for(i = 1; i <= n; ++i) printf("%d ", sa[i]);
        return 0;
    }
}

namespace _kmp {
    int pre[N], n, m;
    char str1[N], str2[N];
    void kmp() {
        for(int i = 2, j = 0; i <= m; i++) {
            while(j && str2[i] != str2[j+1]) j = pre[j];
            if(str2[i] == str2[j+1]) j++;
            pre[i] = j;
        }
        for(int i = 1, j = 0; i <= n; i++) {
            while(j && str1[i] != str2[j+1]) j = pre[j];
            if(str1[i] == str2[j+1]) j++;
            if(j == m) j = pre[j];
        }
    }
}

namespace manachar {
    char s[N], mana[N];
    int len, cnt, p[N], ans, mx, mid;
    void change() {
        mana[++cnt] = '^';
        mana[++cnt] = '$';
        for(int i = 1; i <= len; i++) {
            mana[++cnt] = s[i];
            mana[++cnt] = '$';
        }
        mana[++cnt] = '*';
    }
    void solve() {
        mid = 2; mx = 2;
        for(int i = 2; i < cnt; i++) {
            if(i < mx) p[i] = min(p[2 * mid - i], mx - i);
            else p[i] = 1;
            while(mana[i + p[i]] == mana[i - p[i]]) p[i]++;
            if(i + p[i] > mx) mx = i + p[i], mid = i;
            ans = max(ans, p[i] - 1);
        }
    }
}

namespace _strhash {
    const ull bas = 131;
    int n;
    ull has[10010];
    char s[1600];
    int main() {
        scanf("%d", &n);
        for(int i = 1; i <= n; i++) {
            scanf("%s", s+1);
            int m = strlen(s+1);
            for(int j = 1; j <= m; j++) {
                has[i] = has[i] * bas + (ull)s[j];
            }
        }
        sort(has+1, has+1+n);
        int ans = 1;
        for(int i = 1; i < n; i++)
            if(has[i] != has[i+1]) ans++;
        printf("%d\n", ans);
        return 0;
    }
}

namespace _edge {
    int nxt[N], to[N], h[N], e[N], cnt;
    void init() { memset(h, 0, sizeof(h)); cnt = 0; }
    void add(int u, int v, int w) {
        ++cnt; nxt[cnt] = h[u]; h[u] = cnt; to[cnt] = v; e[cnt] = w;
    }
}

namespace _fuhuan {
    using namespace _edge;
    int vis[N], dis[N], in[N], n;
    bool spfa() {
        memset(vis, 0, sizeof(vis));
        memset(dis, 0x3f, sizeof(dis));
        memset(in, 0, sizeof(in));
        queue<int> q;
        vis[1] = 1; dis[1] = 0;
        q.push(1);
        while(!q.empty()) {
            int u = q.front(); q.pop();
            vis[u] = 0;
            for(int i = h[u]; i; i = nxt[i]) {
                int v = to[i];
                if(dis[v] > dis[u] + e[i]) {
                    dis[v] = dis[u] + e[i];
                    if(!vis[v]) {
                        q.push(v); 
                        vis[v] = 1;
                        if(++in[v] > n) return true;
                    }
                }
            }
        }
        return false;
    }
}
namespace _scc {
    using namespace _edge;
    int dfn[N], low[N], num, s[N], ins[N], d[N], cnum, top, c[N], A[N], a[N], n;
    vector<int> scc[N];
    void tarjan(int u){
        dfn[u] = low[u] = ++num;
        s[++top] = u; ins[u] = 1;
        for(int i = h[u]; i; i = nxt[i]){
            int v = to[i];
            if(!dfn[v]){
                tarjan(v);
                low[u] = min(low[u], low[v]);
            }
            else if(ins[v])
                low[u] = min(low[u], dfn[v]);
        }
        if(dfn[u] == low[u]){
            cnum++; int v;
            do{
                v = s[top--]; ins[v] = 0;
                c[v] = cnum; scc[cnum].push_back(v);
                A[cnum] += a[v];
            }while(u != v);
        }
    }
    int to_c[N], h_c[N], nxt_c[N], cnt_c;
    void add_c(int u,int v){
        cnt_c++; to_c[cnt_c] = v; nxt_c[cnt_c] = h_c[u]; h_c[u] = cnt_c;
    }
    int main() {
        for(int i=1;i<=n;i++)if(!dfn[i])tarjan(i);
        for(int u=1;u<=n;u++)
            for(int i=h[u];i;i=nxt[i]){
                int v=to[i];
                if(c[u]==c[v])continue;
                add_c(c[u],c[v]);
                in[c[v]]++;
            }
        return 0;
    }
}