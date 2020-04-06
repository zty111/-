#include <cstdio>
#include <iostream>
#include <queue>
#include <cstring>
using namespace std;
const int N = 100010, inf = 0x3f3f3f3f;
// 网络流建边，多维护流量限制，当前流量，费用
namespace _edge {
    int cap[N], flow[N], to[N], h[N], nxt[N], cost[N], cnt = 1;
    void add(int u, int v, int ca, int co = 0, int fl = 0) {
        ++cnt; nxt[cnt] = h[u]; h[u] = cnt; to[cnt] = v;
        cap[cnt] = ca; cost[cnt] = co; flow[cnt] = fl; 
    }
}

// 最大流
// dinic算法，先用bfs分层，再用dfs多路增广
namespace _dinic {
    using namespace _edge;
    int d[N], s, t, n, cur[N]; // 当前弧优化
    bool bfs() { // bfs分层
        d[s] = 1;
        queue<int> q; q.push(s);
        while(!q.empty()) {
            int u = q.front(); q.pop();
            for(int i = h[u]; i; i = nxt[i])
                if(!d[to[i]] && cap[i] > flow[i])
                    d[to[i]] = d[u] + 1, q.push(to[i]);
        } return d[t];
    }
    int dfs(int u, int a) { // a流量限制，返回最大流量
        int flo = 0, f = 0; 
        if(a == 0 || u == t) return a;
        for(int & i = cur[u]; i; i = nxt[i])
            if(d[to[i]] == d[u] + 1)
                if((f = dfs(to[i], min(a, cap[i] - flow[i]))) > 0) {
                    flo += f; a -= f; 
                    flow[i] += f; flow[i ^ 1] -= f;
                    if(a == 0) break;
                }
        return flo;
    }
    int maxflow() {
        int ans = 0;
        while(bfs()) {
            for(int i = 1; i <= n; ++i) cur[i] = h[i];
            ans += dfs(s, inf);
        }
        return ans;
    }
}
// ISAP算法，速度快
namespace _isap {
    using namespace _edge; // cnt = 1;
    int vis[N], d[N], s, t, n, cur[N], p[N], num[N];
    void bfs() { // bfs分层
        memset(vis, 0, sizeof(vis));
        d[t] = 0; vis[t] = 1;
        queue<int> q; q.push(t);
        while(!q.empty()) {
            int u = q.front(); q.pop();
            for(int i = h[u]; i; i = nxt[i])
                if(!vis[to[i]] && cap[i] > flow[i])
                    vis[to[i]] = 1, d[to[i]] = d[u] + 1, q.push(to[i]);
        } 
    }
    int augment() {
        int a = inf;
        for(int x = t; x != s; x = to[p[x] ^ 1]) a = min(a, cap[p[x]] - flow[p[x]]);
        for(int x = t; x != s; x = to[p[x] ^ 1]) flow[p[x]] += a, flow[p[x] ^ 1] -= a;
        return a;
    }
    int maxflow() {
        bfs();
        for(int i = 0; i <= n; ++i) num[i] = 0, cur[i] = h[i];
        for(int i = 1; i <= n; ++i) ++num[d[i]];
        int x = s, flo = 0;
        while(d[s] < n) {
            if(x == t) flo += augment(), x = s;
            int ok = 0;
            for(int & i = cur[x]; i; i = nxt[i])
                if(cap[i] > flow[i] && d[x] == d[to[i]] + 1) {
                    ok = 1; p[to[i]] = i; x = to[i];
                    break;
                }
            if(!ok) {
                int mm = n - 1;
                for(int i = h[x]; i; i = nxt[i])
                    if(cap[i] > flow[i]) mm = min(mm, d[to[i]]);
                if(--num[d[x]] == 0) break; // gap优化
                d[x] = mm + 1; ++num[d[x]];
                cur[x] = h[x];
                if(x != s) x = to[p[x] ^ 1];
            }
        }
        return flo;
    }
}

// 费用流
// EK算法，spfa增广，维护路径然后返回计算费用
namespace _EK {
    using namespace _edge; // cnt = 1;
    int n, d[N], s, t, p[N], a[N], vis[N];
    bool EK(int & flo, long long & co) {
        for(int i = 1; i <= n; ++i) d[i] = inf, vis[i] = 0;
        queue<int> q; q.push(s);
        d[s] = 0; vis[s] = 1; p[s] = 0; a[s] = inf;
        while(!q.empty()) {
            int u = q.front(); q.pop();
            vis[u] = 0;
            for(int i = h[u]; i; i = nxt[i])
                if(cap[i] > flow[i] && d[to[i]] > d[u] + cost[i]) {
                    d[to[i]] = d[u] + cost[i];
                    p[to[i]] = i;
                    a[to[i]] = min(a[u], cap[i] - flow[i]);
                    if(!vis[to[i]]) q.push(to[i]), vis[to[i]] = 1;
                }
        }
        if(d[t] == inf) return false;
        flo += a[t]; co += 1ll * d[t] * a[t];
        for(int u = t; u != s; u = to[p[u] ^ 1]) 
            flow[p[u]] += a[t], flow[p[u] ^ 1] -= a[t];
        return true;
    }
    int mincostMaxflow(long long & co) {
        int flo = 0; co = 0;
        while(EK(flo, co));
        return flo;
    }
}
// zkw算法，速度快
namespace _zkw {
    using namespace _edge;
    int co, flo, t, s, n, mi, vis[N];
    int augment(int u, int a) { // dfs搜索
        if(u == t) {co += mi * a; flo += a; return a;}
        vis[u] = 1; int f = 0;
        for(int i = h[u]; i; i = nxt[i])
            if(flow[i] < cap[i] && !cost[i] && !vis[to[i]]) {
                int d = augment(to[i], min(f, cap[i] - flow[i]));
                flow[i] += d; flow[i ^ 1] -= d; f -= d;
                if(!f) return a;
            }
        return a - f;
    }
    bool modlabel() {
        int d = inf;
        for(int i = 1; i <= n; ++i) if(vis[i])
            for(int j = h[i]; j; j = nxt[j])
                if(cap[j] > flow[j] && !vis[to[j]] && cost[j] < d) d = cost[j];
        if(d == inf) return false;
        for(int i = 1; i <= n; ++i) if(vis[i])
            for(int j = h[i]; j; j = nxt[j])
                cost[j] -= d, cost[j ^ 1] += d;
        mi += d;
        return true;
    }
    void zkw() {
        do 
            do memset(vis, 0, sizeof(vis)); 
            while(augment(s, inf));
        while(modlabel());
    }
}