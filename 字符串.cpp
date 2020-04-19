#include <cstdio>
#include <iostream>
#include <cstring>
using namespace std;
const int N = 1e6 + 10;
// 后缀自动机SAM
// 用于匹配后缀，可以建树进行字符串有关dp
// 每个节点包含后缀长，后缀指针，转移，记录新节点
namespace _sam {
    struct node {
        int len, nxt[26], link;
    }sam[N];
    int cnt, last;
    void extend(int c) {
        int cur = ++cnt, p = last;
        sam[cur].len = sam[p].len + 1;
        while(p && !sam[p].nxt[c]) {
            sam[p].nxt[c] = cur;
            p = sam[p].link;
        }
        if(!p) sam[cur].link = 1;
        else {
            int q = sam[p].nxt[c];
            if(sam[p].len + 1 == sam[q].len) sam[cur].link = q;
            else {
                int clone = ++cnt;
                sam[clone] = sam[q];
                sam[clone].len = sam[p].len + 1;
                while(p && sam[p].nxt[c] == q) {
                    sam[p].nxt[c] = clone;
                    p = sam[p].link;
                }
                sam[q].link = sam[cur].link = clone;
            }
        }
        last = cur;
    }
}