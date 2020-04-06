#include <cstdio>
#include <iostream>
#include <queue>
#include <vector>
#include <cmath>
using namespace std;
const int N = 1e5 + 10, inf = 0x3f3f3f3f;
typedef pair<int, int> pii;
#define mp(a, b) make_pair(a, b)

// 链式前向星连边
namespace _edge {
    int h[N], nxt[N << 1], to[N << 1], e[N << 1], cnt;
    void add(int a, int b, int c = 0) {
        ++cnt; nxt[cnt] = h[a]; h[a] = cnt; to[cnt] = b; e[cnt] = c;
    } // 加边
    void clear() {
        cnt = 0; memset(h, 0, sizeof(h));
    } // 清空
    void dfs(int u, int fa) {
        for(int i = h[u]; i; i = nxt[i]) {
            int v = to[i];
            dfs(v, u);
        }
    } // dfs遍历
}

// 最小生成树
// kruskal算法，排序，每次加最小边，用并查集维护树结构
namespace _kruskal {
    int f[N], e[N], m, u[N], v[N], r[N];
    int find(int x) { return f[x] == x ? x : f[x] = find(f[x]); }
    bool cmp(int a, int b) { return e[a] < e[b]; }
    void kruskal() {
        for(int i = 1; i <= m; ++i) r[i] = f[i] = i;
        sort(r + 1, r + 1 + m, cmp);
        for(int i = 1; i <= m; ++i) {
            int fa = find(u[r[i]]), fb = find(v[r[i]]);
            if(fa != fb) f[fa] = fb;// 加入最小生成树
        }
    }
}
// prim算法，每次加距离最小生成树最近的点，用堆维护
namespace _prim {
    using namespace _edge;
    priority_queue<pii, vector<pii>, greater<pii> > q;
    bool vis[N]; int d[N], n;
    void prim() {
        for(int i = 1; i <= n; ++i) d[i] = inf;
        d[1] = 0; q.push(mp(0, 1));
        while(!q.empty()) {
            int u = q.top().second; q.pop();
            if(vis[u]) continue;
            vis[u] = 1; // 加入最小生成树
            for(int i = h[u]; i; i = nxt[i])
                if(d[to[i]] > e[i]) d[to[i]] = e[i], q.push(mp(e[i], to[i]));
        }
    }
}

// 最短路
// dijkstra算法，不能有负权边，用堆维护到每个点的最短距离，出堆时为最短路
namespace _dijkstra {
    using namespace _edge;
    int n, vis[N], dis[N];
    priority_queue<pii, vector<pii>, greater<pii> > q;
    void dijkstra(int s) {
        for(int i = 1; i <= n; ++i) dis[i] = inf, vis[i] = 0;
        dis[s] = 0; q.push(mp(0, s));
        while(!q.empty()) {
            int u = q.top().second; q.pop();
            if(vis[u]) continue;
            vis[u] = 1;
            for(int i = h[u]; i; i = nxt[i]) {
                int v = to[i];
                if(dis[v] > dis[u] + e[i]) dis[v] = dis[u] + e[i], q.push(mp(dis[v], v));
            }
        }
    }
}
// spfa算法，用队列维护，每次最短路径更新则入队，容易被卡
// #1为SLF优化，利用双端队列优化，比队首dis小就放队首，否则放队尾
// #2为LLL优化，双端队列，出队时比较与平均dis的大小，大于则不出队放队尾
namespace _spfa {
    using namespace _edge;
    int dis[N], n, inq[N];
    queue<int> q; // #1|#2 deque<int> q;
    void spfa(int s) {
        for(int i = 1; i <= n; ++i) dis[i] = inf;
        dis[s] = 0; inq[s] = 1;
        q.push(s); // #1|#2 q.push_front(s);
        // #2 long long qsz = 1, sum = 0;
        while(!q.empty()) {
            int u = q.front(); q.pop(); // #1|#2 q.pop_front();
            // #2 if(dis[u] * qsz > sum) {q.push_back(v); continue;}
            // #2 sum -= dis[u]; --qsz;
            inq[u] = 0;
            for(int i = h[u]; i; i = nxt[i]) {
                int v = to[i];
                if(dis[v] > dis[u] + e[i]) {
                    dis[v] = dis[u] + e[i];
                    if(!inq[v]) {
                        q.push(v); inq[v] = 1;
                        /* #1 if(!q.empty() && dis[v] < dis[q.front()]) q.push_front(v);
                              else q.push_back(v); */
                        // #2 sum += dis[v]; ++qsz;
                    }
                }
            }
        }
    }
}
// floyd算法，求解多对点之间最短路，不能有负环
namespace floyd {
    int n, dis[N][N]; // dis[i][i] = 0, dis[i][j] = e(i, j)
    void floyd() {
        for(int k = 1; k <= n; ++k) // 枚举转移点
            for(int i = 1; i <= n; ++i)
                for(int j = 1; j <= n; ++j)
                    dis[i][j] = min(dis[i][j], dis[i][k] + dis[k][j]);
    }
}
// johnson算法，求全源最短路，不能有负环
// 新建0号点，向其他点连边权为0的边，用spfa预处理0号点到其他点的最短路h[]
// 原图边权重置为 e[i] + h[u] - h[v] > 0，以每个点为起点作dijkstra()
namespace _johnson {
    using namespace _spfa;
    using namespace _dijkstra;
    int n, m, u[N], v[N], w[N], ans[N][N];
    void johnson() {
        for(int i = 1; i <= n; ++i) add(n + 1, n, 0);
        spfa(n + 1);
        clear();
        for(int i = 1; i <= m; ++i) 
            add(u[i], v[i], w[i] + _spfa::dis[u[i]] - _spfa::dis[v[i]]);
        for(int i = 1; i <= n; ++i) {
            dijkstra(i);
            for(int j = 1; j <= n; ++j)
                ans[i][j] = _dijkstra::dis[j] - _spfa::dis[i] + _spfa::dis[j]; 
        }
    }
}

// 2-SAT
// 搜索，一个点被选择则它连接的所有点都被选择，真假同时选中时不可行，不用回溯
namespace _2Sat {
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
    // 加条件，0为假1为真，原条件和逆否条件
    void add_clause(int x, int xval, int y, int yval) {
        x = (x << 1) + xval;
        y = (y << 1) + yval;
        G[x ^ 1].push_back(y);
        G[y ^ 1].push_back(x);
    }
}

// 负环，用spfa判定，一个点更新超过n次则有负环，需保证图连通
namespace _fuHuan {
    using namespace _edge;
    int vis[N], dis[N], in[N], n;
    queue<int> q;
    bool spfa() {
        for(int i = 1; i <= n; ++i) dis[i] = inf, in[i] = 0;
        vis[1] = 1; dis[1] = 0; q.push(1); in[1] = 1; // 1点开始有1次
        while(!q.empty()) {
            int u = q.front(); q.pop();
            vis[u] = 0;
            for(int i = h[u]; i; i = nxt[i]) {
                int v = to[i];
                if(dis[v] > dis[u] + e[i]) {
                    dis[v] = dis[u] + e[i];
                    if(++in[v] > n) return true; // 被更新次数+1
                    if(!vis[v]) q.push(v), vis[v] = 1;
                }
            }
        }
        return false;
    }
}

// 差分约束系统，每个约束条件为 xi - xj <= ck 求一组满足所有条件的解
// 每个条件由 j 向 i 连边，长为ck，有负环则无解，否则一组解为d[]
namespace _chaFenYueShu {
    using namespace _fuHuan;
    int u, v, c, m;
    int main() {
        // u - v <= c，其他形式变化为这个
        for(int i = 1; i <= m; ++i) add(u, v, c);
        if(spfa()) printf("No Solution!");
        else for(int i = 1; i <= n; ++i) printf("%d ", dis[i]);
        return 0;
    }
}

// 拓补排序，图为DAG，每次加入入度为0的点，其到达的点入度-1
namespace _topo {
    using namespace _edge;
    int in[N], u, v, w, n, que[N], r;
    queue<int> q;
    void topo() {
        for(int i = 1; i <= n; ++i) if(!in[i]) q.push(i);
        while(!q.empty()) {
            int u = q.front(); q.pop();
            que[++r] = u;
            for(int i = h[u]; i; i = nxt[i])
                if(--in[to[i]] == 0) q.push(to[i]);
        }
    }
    int main() {
        add(u, v, w); ++in[v]; // 统计入度
        topo();
        return 0;
    }
}

// 强连通分量scc，有向图中可以互相到达的点在同一强连通分量里，缩点后为DAG
// tarjan算法，维护dfn时间戳，low为能到达的最小dfn，dfn = low时之后访问的点在一个scc里，用栈维护
namespace _tarjan {
    using namespace _edge;
    int dfn[N], low[N], s[N], top, num, ins[N];
    vector<int> scc[N]; int cnum, c[N];
    void tarjan(int u) {
        dfn[u] = low[u] = ++num;
        s[++top] = u; ins[u] = 1;
        for(int i = h[u]; i; i = nxt[i]) {
            int v = to[i];
            if(!dfn[v]) tarjan(v), low[u] = min(low[u], low[v]);
            else if(ins[v]) low[u] = min(low[u], dfn[v]);
        }
        if(dfn[u] == low[u]) {
            ++cnum; int v;
            do {
                v = s[top--]; ins[v] = 0;
                c[v] = cnum; scc[cnum].push_back(v);
            } while(u != v);
        }
    }
}

// 双连通分量dcc，无向图
// 边双连通分量e-dcc，不存在桥的无向连通图，求出所有桥后删去
// tarjan算法，求桥（删去后分裂成两个图的边），dfn[u] < low[v]时，v无法到达u及之前的点，(u, v)为桥
namespace _bridge {
    using namespace _edge; // cnt = 1 方便标记边与反边
    int dfn[N], low[N], num, bridge[N];
    void tarjan(int u, int in) {
        dfn[u] = low[u] = ++num;
        for(int i = h[u]; i; i = nxt[i]) {
            int v = to[i];
            if(!dfn[v]) {
                tarjan(v, i);
                low[u] = min(low[u], low[v]);
                if(low[v] > dfn[u]) bridge[i] = bridge[i ^ 1] = 1;
            } else if(i != (in ^ 1)) low[u] = min(low[u], dfn[v]); // 处理重边，只有入边不能更新
        }
    }
}
// 标记边双连通，缩点后为树
namespace _edcc {
    using namespace _bridge;
    int c[N], n, dcc;
    void dfs(int u) {
        c[u] = dcc;
        for(int i = h[u]; i; i = nxt[i]) {
            int v = to[u];
            if(c[v] || bridge[i]) continue;
            dfs(v);
        }
    }
    int main() {
        for(int i = 1; i <= n; ++i) if(!c[i]) ++dcc, dfs(i);
        return 0;
    }
}
// 点双连通分量v-dcc，不存在割点的无向联通图，但割点可能属于多个v-dcc，不能直接去除割点
// tarjan算法，求割点（删去后分成两个图的点），dfn[u] <= low[v]时，不能回到祖先，u为割点
// 注意：根节点需要至少2个子节点满足条件
namespace _cut {
    using namespace _edge;
    int dfn[N], low[N], num, cut[N], root;
    void tarjan(int u) {
        dfn[u] = low[u] = ++num;
        int flag = 0; // 满足条件的子节点
        for(int i = h[u]; i; i = nxt[i]) {
            int v = to[i];
            if(!dfn[v]) {
                tarjan(v);
                low[u] = min(low[u], low[v]);
                if(low[v] >= dfn[u])
                    if(u != root || ++flag > 1) cut[u] = 1; // 特判根节点
            } else low[u] = min(low[u], dfn[v]);
        }
    }
}
// tarjan算法，求v-dcc，用栈维护，第一次访问时入栈，满足割点判定条件时出栈，构成v-dcc
// 无需特殊处理根节点
namespace _vdcc {
    using namespace _edge;
    int dfn[N], low[N], num, cut[N], root, s[N], top;
    vector<int> dcc[N]; int dcnt;
    void tarjan(int u) {
        dfn[u] = low[u] = ++num;
        s[++top] = u;
        if(u == root && h[u] == 0) dcc[++dcnt].push_back(u); // 孤立点自成一个v-dcc
        int flag = 0; // 满足条件的子节点
        for(int i = h[u]; i; i = nxt[i]) {
            int v = to[i];
            if(!dfn[v]) {
                tarjan(v);
                low[u] = min(low[u], low[v]);
                if(low[v] >= dfn[u]) {
                    if(u != root || ++flag > 1) cut[u] = 1; // 特判根节点
                    ++dcnt; int x;
                    do {
                        x = s[top--];
                        dcc[dcnt].push_back(x);
                    } while(x != v);
                    dcc[dcnt].push_back(u); // 割点也在v-dcc中
                }
            } else low[u] = min(low[u], dfn[v]);
        }
    }
}
// v-dcc的缩点，每个割点新建一个点，向包含它的所有v-dcc连边，缩点后为树
namespace _suoDian {
    using namespace _vdcc;
    int n, id[N], c[N];
    int main() {
        num = dcnt;
        for(int i = 1; i <= n; ++i) if(cut[i]) id[i] = ++num; // 复制割点
        clear();
        for(int i = 1; i <= dcnt; ++i)
            for(int j = 0; j < dcc[i].size(); ++j) {
                int u = dcc[i][j];
                if(cut[u]) add(i, id[u]), add(id[u], i);
                else c[u] = i; // 除割点外，其他点在一个v-dcc中
            }
        return 0; 
    }
}

// 二分图，节点在两个集合中，每个集合内部无边，黑白染色后边连接黑点和白点，不存在长度为奇数的环
// 匈牙利算法，每次选未匹配点，若另一个点已匹配，则尝试更改匹配
namespace _match {
    using namespace _edge;
    int vis[N], matched[N], n;
    bool find(int u) {
        for(int i = h[u]; i; i = nxt[i]) {
            int v  = to[i];
            if(vis[v]) continue;
            vis[v] = 1; // 每个点只匹配一次
            if(!matched[v] || find(matched[v])) { // 尝试更改
                matched[v] = u; 
                return true;
            }
        }
        return false;
    }
    int match() {
        int ans = 0;
        memset(matched, 0, sizeof(matched));
        for(int i = 1; i <= n * 2; ++i) {
            memset(vis, 0, sizeof(vis)); // 每个点尝试
            if(find(i)) ++ans;
        } return ans;
    }
}

// 树的最近公共祖先lca
// 倍增算法，bfs求2^i祖先，求lca先拉到同一高度，然后同时上移，直到父亲为lca
namespace _lca {
    using namespace _edge;
    queue<int> q;
    int d[N], f[N][25], n, s, t;
    void bfs(int s) {
        d[s] = 1; q.push(s);
        while(!q.empty()) {
            int u = q.front(); q.pop();
            for(int i = h[u]; i; i = nxt[i]) {
                int v = to[i];
                if(d[v]) continue;
                d[v] = d[u] + 1;
                f[v][0] = u;
                for(int j = 1; j <= t; ++j) f[v][j] = f[f[v][j - 1]][j - 1];
                q.push(v);
            }
        }
    }
    int lca(int x, int y) {
        if(d[x] > d[y]) swap(x, y); // y 更深
        for(int i = t; i >= 0; --i) if(d[f[y][i]] >= d[x]) y = f[y][i]; // 使x, y同深
        if(x == y) return x;
        for(int i = t; i >= 0; --i) if(f[y][i] != f[x][i]) x = f[x][i], y = f[y][i]; // 同时上移
        return f[x][0];
    }
    int main() {
        t = (int) (log(n) / log(2)) + 1;
        bfs(s); return 0;
    }
}
// 树剖算法，速度快, dfs1维护深度、子节点数、父亲、重儿子，dfs2维护重链端点
namespace __lac {
    using namespace _edge;
    int siz[N], f[N], son[N], dep[N], top[N];
    void dfs1(int u, int fa, int deep) {
        dep[u] = deep; f[u] = fa; son[u] = 1;
        for(int i = h[u]; i; i = nxt[i]) {
            int v = to[i];
            if(v == fa) continue;
            dfs1(v, u, deep + 1);
            siz[u] += siz[v];
            if(siz[v] > siz[son[u]]) son[u] = v;
        }
    }
    void dfs2(int u, int topf) {
        top[u] = topf;
        if(!son[u]) return;
        dfs2(son[u], topf);
        for(int i = h[u]; i; i = nxt[i])
            if(to[i] != f[u] && to[i] != son[u]) dfs2(to[i], to[i]);
    }
    int lca(int x, int y) {
        while(top[x] != top[y]) {
            if(dep[top[x]] < dep[top[y]]) swap(x, y);
            x = f[top[x]];
        } // 拉到一个重链上
        if(dep[x] > dep[y]) swap(x, y); // 选深度小的
        return x;
    }
}

// 树的重心 子树节点最小的点，树形dp维护子树大小
namespace _centroid {
    using namespace _edge;
    int siz[N], rt, wt[N], n;
    void centroid(int u, int fa) {
        siz[u] = 1;
        for(int i = h[u]; i; i = nxt[i]) {
            int v = to[i];
            if(v == fa) continue;
            centroid(v, u);
            siz[u] += siz[v];
            wt[u] = max(wt[u], siz[v]);
        }
        wt[u] = max(wt[u], n - siz[u]);
        if(rt == 0 || wt[u] < wt[rt]) rt = u;
    }
}

// 树的直径 树中两个节点之间最远距离，树形dp维护到此点的最大距离，或bfs求一端，再bfs求另一端
namespace _diam {
    using namespace _edge;
    int ans, d[N], vis[N], n, pre[N];
    queue<int> q;
    void dp(int u) {
        vis[u] = 1;
        for(int i = h[u]; i; i = nxt[i]) {
            int v = to[i];
            if(vis[v]) continue;
            dp(v);
            ans = max(ans, d[u] + d[v] + e[i]);
            d[u] = max(d[u], d[v] + e[i]);
        }
    }
    int bfs(int s){
        for(int i = 1; i <= n; ++i) vis[i] = pre[i] = 0, d[i] = -1;
        q.push(s); d[s] = 0; vis[s] = 1;
        while(!q.empty()) {
            int u = q.front(); q.pop();
            for(int i = h[u]; i; i = nxt[i]) {
                int v = to[i];
                if(vis[v]) continue;
                vis[v] = 1;
                d[v] = d[u] + 1;
                pre[v] = i; // 可反推直径上的点
                q.push(v);
            }
        }
        int x = 1;
        for(int i = 2; i <= n; ++i) if(d[i] < d[x]) x = i; // 距离最大的为一端
        return x;
    }
}

// k短路，A*算法，用最短路做估价函数
namespace _Astar {
    using namespace _dijkstra;
    int g[N], h[N], siz[N], k;
    int v[N], u[N], w[N], s, t, m, n;
    priority_queue<pii, vector<pii>, vector<pii> > q;
    int Astar() {
        for(int i = 1; i <= n; ++i) g[i] = inf;
        g[s] = 0; q.push(mp(h[s], s));
        while(!q.empty()) {
            int u = q.top().second; q.pop();
            ++siz[u];
            if(u == t && siz[u] == k) return g[u]; // 第k次到达终点
            if(u > k) continue; // 路径上的点最多经过k次
            for(int i = h[u]; i; i = nxt[i]) {
                int v = to[i];
                if(g[v] > g[u] + e[i]) g[v] = g[u] + e[i], q.push(mp(g[v] + h[v], v));
            }
        }
    }
    int main() {
        for(int i = 1; i <= m; ++i) add(v[i], u[i], w[i]); // 建反图跑dijkstra求h[]
        dijkstra(t);
        for(int i = 1; i <= n; ++i) h[i] = dis[i];
        clear();
        for(int i = 1; i <= m; ++i) add(u[i], v[i], w[i]); // 原图跑A*
        cout<<Astar()<<endl;
        return 0;
    }
}

// 最小树形图，有向图的最小生成树，朱刘算法
namespace _zhuliu {
    using namespace _edge;
    int pre[N], in[N], vis[N], id[N], n, m;
    int u[N], v[N], w[N], root;
    int zhuliu() {
        int ans = 0;
        while(1) {
            for(int i = 1; i <= n; ++i) in[i] = inf;
            for(int i = 1; i <= m; ++i) 
                if(w[i] < in[v[i]] && u[i] != v[i]) pre[v[i]] = i, in[v[i]] = w[i]; // 找最小入边 
            for(int i = 1; i <= n; ++i) if(i != root && in[i] == inf) return -1; // 除根外不能有孤立点
            int ccnt = 0; in[root] = 0; memset(id, 0, sizeof(id)); memset(vis, 0, sizeof(vis)); // 找环
            for(int i = 1; i <= n; ++i) {
                ans += in[i];
                int y = i;
                while(vis[y] != i && !id[y] && y != root) vis[y] = i, y = pre[y];
                if(y != root && !id[y]) {
                    id[y] = ++ccnt;
                    for(int x = pre[y]; x != y; x = pre[x]) id[x] = ccnt;
                }
            }
            if(!ccnt) break; // 无环结束
            for(int i = 1; i <= n; ++i) if(!id[i]) id[i] = ++ccnt; // 孤立点
            for(int i = 1; i <= m; ++i) {
                if(id[u[i]] != id[v[i]]) w[i] -= in[v[i]]; // 减去计入答案的边权
                u[i] = id[u[i]]; v[i] = id[v[i]];
            }
            n = ccnt; // 剩余点数
            root = id[root];
        }
        return ans;
    }
}

// 欧拉通路，弗罗莱算法 恰有2个点入度为奇数
namespace _fleury {
    int s[N], top, n, m, st; // st为入度为奇数的点
    int g[N][N]; // 邻接矩阵
    void dfs(int x) {
        s[++top] = x;
        for(int i = 1; i <= n; ++i) if(g[x][i]) {
            g[x][i] = g[i][x] = 0; // 删边
            dfs(i); break;
        } 
    }
    void fleury() {
        int bridge; top = 0;
        s[++top] = st;
        while(top) {
            bridge = 1;
            for(int i = 1; i <= n; ++i)
                if(g[s[top]][i]) {
                    bridge = 0;
                    break;
                }
            if(bridge) printf("%d ", s[top--]);
            else dfs(s[top--]);
        }
    }
}
// 更快的算法
namespace _hierholzer{
    using namespace _edge; // cnt = 1;
    bool vis[N]; int s[N], top;
    void dfs(int u) {
        for(int i = h[u]; i; i = nxt[i])
            if(!vis[i]) vis[i] = vis[i ^ 1] = 1, dfs(to[i]);
        s[++top] = u;
    }
    void print() {while(top) printf("%d ", s[top--]);}
}

// 虚树
namespace _xushu {
    using namespace _lca;
    using namespace _edge;
    int dfn[N], s[N], a[N], _dfn, k, top;
    void dfs(int u, int fa) {
        dfn[u] = ++_dfn;
        for(int i = h[u]; i; i = nxt[i]) if(to[i] != fa) dfs(to[i], u);
    }
    bool cmp(int a, int b) { return dfn[a] < dfn[b]; }
    void build() {
        dfs(1, 0);
        sort(a + 1, a + 1 + k, cmp);
        s[++top] = 1; h[1] = 0;
        for(int i = 1; i <= k; ++i) if(a[i] != 1) {
            int l = lca(a[i], s[top]);
            if(l != s[top]) {
                while(dfn[l] < dfn[s[top - 1]]) add(s[top - 1], s[top]), --top;
                if(dfn[l] > dfn[s[top - 1]]) h[l] = 0, add(l, s[top]), s[top] = l;
                else add(l, s[top--]);
            }
            h[a[i]] = 0; s[++top] = a[i];
        }
        for(int i = 1; i < top; ++i) add(s[i], s[i + 1]);
    }
}