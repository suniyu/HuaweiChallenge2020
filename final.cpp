#include<bits/stdc++.h>
#include <sys/mman.h>
using namespace std;
#define cur_time() (chrono::system_clock::now().time_since_epoch().count() / 1e9)
 
#define DEBUG
 
typedef unsigned long long u64;
typedef unsigned int u32;
typedef uint16_t u16;
typedef double CalcType;

const u32 NThread = 12;
const u32 MAX_N = 2000111, MAX_M = 2500111;
const u32 inf = (1ull << 16) - 1;
const u32 Max_Weight = (1 << 21) - 1;

bool type_switch = 0;

//int input_file = open("/data/test_data.txt", O_RDONLY);
//FILE* output_file = fopen(/projects/student/result.txt", "w");

bool pointer_switch = 0;


const size_t max_id = 1 << 16;
const size_t max_each_num = 1 << 16;
const size_t max_total = max_id * max_each_num;

struct EdgeInque{
	u16 dis;
	int to;
};

struct MH{
	struct PQ{
		EdgeInque QB[MAX_M];
		EdgeInque *begin = QB, *end = QB;
		inline void push(const EdgeInque &x)
		{
			*(end++) = x;
			push_heap(begin, end);
		}
		inline void pop()
		{
			pop_heap(begin, end);
			end--;
		}
		inline EdgeInque top()
		{
			return *begin;
		}
		inline bool empty()
		{
			return begin == end;
		}
	}PQ;
	char *buffer;
	int p[max_id];
	int cur;
	u16 max_key;
	MH()
	{
		buffer = (decltype(buffer))mmap64(NULL, max_total, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
		memset(p, 0, sizeof(p));
		cur = 0;
		max_key = 0;
	}
	__inline void push(const u16 &x, const int &u)
	{
		if(x >= max_id)
		{
			PQ.push({x, u});
			return;
		}
		((int *)(buffer + max_each_num * x))[p[x]++] = u;
		max_key = max(x, max_key);
	}
	__inline bool pop(u16 &x, int &u)
	{
		while (!p[cur])
		{
			cur++;
			if (cur > max_key)
			{
				if(PQ.empty())
					return false;
				x = PQ.top().dis;
				u = PQ.top().to;
				PQ.pop();
				return true;
				
				return false; 
			}
		}
		x = cur;
		u = ((int *)(buffer + max_each_num * x))[--p[x]];
		return true;
	}
	__inline void clear()
	{
		cur = 0;
		max_key = 0;
	}
	~MH() { munmap(buffer, max_total); }
};

int rd[MAX_N], cd[MAX_N];
namespace NW{
	int wt[MAX_N], accessiable[MAX_N];
	int topl_sort[MAX_N];
	bool fucked[MAX_N];
}

unordered_map<int, int> id;

int id_cnt = 0;
u32 redu[MAX_N];

int get_id(int u)
{
	if(id.count(u))
		return id[u];
	id[u] = ++id_cnt;
	redu[id_cnt] = u;
	return id_cnt;
}

struct VectorEdge{
	int to;
	u16 dis;
};

vector<VectorEdge> _G[MAX_N];

struct Vector1{
	VectorEdge *begin, *end;
}G1[MAX_N];
struct Vector2{
	u32 *begin, *end;
}G2[MAX_N];
const int MAX_D = 64;

VectorEdge buffer1[MAX_N * MAX_D];
u32 buffer2[MAX_N * MAX_D];

#define Begin1(u) (pointer_switch?(buffer1 + MAX_D * u + 1) : G1[u].begin)
#define Begin2(u) (pointer_switch?(buffer2 + MAX_D * u + 1) : G2[u].begin)

#define End1(u) (pointer_switch?(buffer1 + MAX_D * u + buffer1[MAX_D * u].to + 1) : G1[u].end)
#define End2(u) (pointer_switch?(buffer2 + MAX_D * u + buffer2[MAX_D * u] + 1) : G2[u].end)
int n;

namespace tarjan{

	int vis[MAX_N], LOW[MAX_N], DFN[MAX_N];
	int size[MAX_N], stack[MAX_N], dye[MAX_N], index = 0;
	int CN = 0;
	int dfs_num = 0;
	int n = 0;
	void tarjan(int pos)
	{
		if(DFN[pos])
			return;
		vis[stack[++index] = pos] = 1;
		LOW[pos] = DFN[pos] = ++dfs_num;
		if(type_switch)
		{
			u32 *_end = End2(pos);
			for(u32* edg = Begin2(pos); edg != _end; ++edg)
			{
				int to = (*edg) & Max_Weight;
				if(!DFN[to])
				{
				    tarjan(to);
				    LOW[pos] = min(LOW[pos],LOW[to]);
				}
				else if(vis[to])
					LOW[pos] = min(LOW[pos],DFN[to]);
			}
		}
		else
		{
			VectorEdge *_end = End1(pos);
			for(VectorEdge* edg = Begin1(pos); edg != _end; ++edg)
			{
				if(!DFN[edg->to])
				{
				    tarjan(edg->to);
				    LOW[pos] = min(LOW[pos],LOW[edg->to]);
				}
				else if(vis[edg->to])
					LOW[pos] = min(LOW[pos],DFN[edg->to]);
			}
		}
		if(LOW[pos] == DFN[pos])
		{
		    vis[pos] = 0;
		    size[dye[pos] = ++CN]++;
		    while(pos != stack[index])
		    {
		        vis[stack[index]] = 0;
		        NW::topl_sort[n--] = stack[index];
		        size[CN]++;
		        dye[stack[index--]] = CN;
		    }
		    NW::topl_sort[n--] = stack[index];
		    index--;
		}
	}
}

struct Mission{
	int s,w;
};
bool operator < (const Mission &A, const Mission &B)
{
	return A.w < B.w;
}

mutex mtx;
priority_queue<Mission> missions;
bool completed[MAX_N], miq[MAX_N];
vector<int> MG[MAX_N];

atomic_int cnt(0), cur_completed(0);
int wtf = 0;
__inline pair<u16, int> nxt_mission(int last)
{
	mtx.lock();
	if(last > 0)
	{
		for(int u: MG[last])
		{
			missions.push({u, -tarjan::dye[u]});
			miq[u] = 1;
		}
	}
	cnt++;
	pair<u16, int> ret;
	bool flag = 1;
	if(last > 0)
		for(auto edg: _G[last])
			if(miq[edg.to] && !completed[edg.to])
			{
				ret = make_pair(edg.dis, edg.to);
				flag = 0;
				#ifdef DEBUG
				wtf++;
				#endif
				break;
			}
	while(flag)
	{
		if(missions.empty())
		{
			ret = make_pair(0, n + 1);
			break;
		}
		ret = make_pair(0, missions.top().s);
		missions.pop();
		if(!completed[ret.second])
			break;
	}
	completed[ret.second] = 1;
	mtx.unlock();
	return ret;
}

bool operator < (const EdgeInque &A, const EdgeInque &B)
{
	return A.dis > B.dis;
}

CalcType pre_div[5050];

class Work_Thread{
public:
	int cur_start;
	int topl_sort[MAX_N], bk[MAX_N];
	int head[MAX_N];
	bool intopl[MAX_N];
	u16 dis[MAX_N];
	u16 path_cnt[MAX_N];
	CalcType cv[MAX_N], ans[MAX_N];
	int topl_cnt = 0;
	
	int edge_cnt = 0;
	
	#ifdef DEBUG
	double last = 0, dij_cnt = 0, other_cnt = 0;
	int times = 0, times1 = 0, times2 = 0;
	double time1 = 0, time2 = 0;
	double ctime()
	{
		double tmp = cur_time();
		double ret = tmp - last;
		last = tmp;
		return ret;
	}
	#endif
	inline void topl_ins(int u)
	{
		if(intopl[u])
			return;
		intopl[u] = 1;
		topl_cnt++;
		topl_sort[topl_cnt] = u;
	}

	MH heap;
	
	/*
	struct PQ{
		EdgeInque QB[MAX_M];
		EdgeInque *begin = QB, *end = QB;
		inline void push(const EdgeInque &x)
		{
			*(end++) = x;
			push_heap(begin, end);
		}
		inline void pop()
		{
			pop_heap(begin, end);
			end--;
		}
		inline EdgeInque top()
		{
			return *begin;
		}
		inline bool empty()
		{
			return begin == end;
		}
	}PQ;
	*/
	bool visited[MAX_N];
	void dij()
	{
		heap.push(1ull, cur_start);
		dis[cur_start] = 1;
		while(1)
		{
			u16 DIS = 0;
			int now = 0;
			while(1)
			{
				if(!heap.pop(DIS, now))
				{
					heap.clear();
					return;
				}
				if(!visited[now])
					break;
			}
			
			visited[now] = 1;
			topl_ins(now);
			if(type_switch)
			{
				u32 *_end = End2(now);
				for(u32* edg = Begin2(now); edg != _end; edg++)
				{
					int to = (*edg)&Max_Weight;
					u16 tmp = DIS + ((*edg) >> 21);
					if(tmp < dis[to])
					{
						dis[to] = tmp;
						heap.push(tmp, to);
						clean(to);
						add_edge(to, now);
					}
					else if(tmp == dis[to])
						add_edge(to, now);
				}
			}
			else
			{
				VectorEdge *_end = End1(now);
				for(VectorEdge* edg = Begin1(now); edg != _end; edg++)
				{
					int to = edg->to;
					u16 tmp = DIS + edg->dis;
					if(tmp < dis[to])
					{
						dis[to] = tmp;
						heap.push(tmp, to);
						clean(to);
						add_edge(to, now);
					}
					else if(tmp == dis[to])
						add_edge(to, now);
				}
			}
		}
		heap.clear();
	}
	#define calc_path(u,v)\
	{\
		path_cnt[v] += path_cnt[u];\
	}
	#define calc_cv(u, v)\
	{\
		cv[u] += cv[v];\
	}
	
	int pre[MAX_N];  // cache hit
	
	struct Edge{
		int to, nxt;
	}edge[MAX_M];
	
	struct Stack{
		int v[MAX_M];
		int last = 0;
		inline bool empty()
		{
			return last == 0;
		}
		inline void clear()
		{
			last = 0;
		}
		inline int top()
		{
			return v[--last];
		}
		inline void push(int x)
		{
			v[last++] = x;
		}
	}sta;
	int got[MAX_M];
	/*
	struct Edge{
		int begin, end;
	}E[MAX_N];
	*/
	inline void add_edge(int u, int v)
	{
		// got[E[u].end++] = v;
		if(!pre[u])
		{
			pre[u] = v;
			return;
		}
		int p;
		if(sta.empty())
			p = ++edge_cnt;
		else
			p = sta.top();
		edge[p].to = v;
		edge[p].nxt = head[u];
		head[u] = p;
	}
	
	inline void clean(int u)
	{
		// E[u].end = E[u].begin;
		pre[u] = 0;
		for(int p = head[u]; p; p = edge[p].nxt)
			sta.push(p);
		head[u] = 0;
	}
	void work(int t)
	{
		int last_start = 0;
		
		for(int i = 1; i <= n; i++)
			dis[i] = inf;
		/*
		for(int i = 1; i <= n; i++)
			E[i].end = E[i].begin = E[i-1].begin + rd[i-1];
		*/
		while(1)
		{
			#ifdef DEBUG
			ctime();
			#endif
			
			auto ret = nxt_mission(last_start);
			if(NW::fucked[last_start])
				ret.first = 0;
			cur_start = ret.second;
			last_start = cur_start;
			
			if(cur_start > n)
				break;
			if(NW::fucked[cur_start]) // special case
			{
				if(type_switch)
				{
					NW::accessiable[cur_start] = NW::accessiable[(*Begin2(cur_start))&Max_Weight] + 1;
					ans[(*Begin2(cur_start))&Max_Weight] += NW::wt[cur_start] * (NW::accessiable[cur_start] - 2);
				}
				else
				{
					NW::accessiable[cur_start] = NW::accessiable[Begin1(cur_start)->to] + 1;
					ans[Begin1(cur_start)->to] += NW::wt[cur_start] * (NW::accessiable[cur_start] - 2);
				}
				continue;
			}
			int _topl_cnt = 0;
			if(ret.first == 0)
			{
				for(int i = 1; i <= topl_cnt; i++)
				{
					dis[topl_sort[i]] = inf;
					visited[topl_sort[i]] = 0;
					head[topl_sort[i]] = 0;
					// E[i].end = E[i].begin;
					intopl[topl_sort[i]] = 0;
					pre[topl_sort[i]] = 0;
				}
				edge_cnt = 0;
				topl_cnt = 0;
				sta.clear();
			}
			else // keep result from last one
			{
				_topl_cnt = topl_cnt;
				for(int i = 1; i <= topl_cnt; i++)
				{
					bk[i]  = topl_sort[i];
					dis[topl_sort[i]] += ret.first;
					visited[topl_sort[i]] = 0;
					intopl[topl_sort[i]] = 0;
				}
				clean(cur_start);
				topl_cnt = 0;
			}
			path_cnt[cur_start] = 1;
			#ifdef DEBUG
			other_cnt += ctime();
			#endif
			dij();
			#ifdef DEBUG
			dij_cnt += ctime();
			#endif
			for(int i = 1; i <= _topl_cnt ; i++)
				topl_ins(bk[i]);
			
			for(int i = 1; i <= topl_cnt; i++)
			{
				int u = topl_sort[i];
				if(u != cur_start)
					path_cnt[u] = 0;
				for(int p = head[u]; p; p = edge[p].nxt)
				{
					int v = edge[p].to;
				/*
				for(int p = E[u].begin; p != E[u].end; p++)
				{
					int v = got[p];
				*/
					calc_path(v, u);
				}
				int v = pre[u];
				if(v != 0)
					calc_path(v, u);
				cv[u] = pre_div[path_cnt[u]];
			}
			for(int i = topl_cnt; i >= 1; i--)
			{
				int u = topl_sort[i];
				for(int p = head[u]; p; p = edge[p].nxt)
				{
					int v = edge[p].to;
				/*
				for(int p = E[u].begin; p != E[u].end; p++)
				{
					int v = got[p];
				*/
					calc_cv(v, u);
				}
				int v = pre[u];
				if(v != 0)
					calc_cv(v, u);
			}
			
			NW::accessiable[cur_start] = topl_cnt;
			
			//cerr << useful_edge <<endl;
			
			for(int i = 1; i <= topl_cnt; i++)
			{
				if(i > 1)
					ans[topl_sort[i]] += NW::wt[cur_start] * (cv[topl_sort[i]] * path_cnt[topl_sort[i]] - 1); // NW::wt   weight of node
			}
			
			#ifdef DEBUG
			other_cnt += ctime();
			cur_completed++;
			if(cur_completed % 500 == 0)
			{
				cerr << cur_completed << " " << dij_cnt << " " << other_cnt << " " << endl;
			}
			#endif
		}
	}
}wthd[NThread];

void *do_it(void *arg)
{
	u64 tmp=(unsigned long long)arg;
	cpu_set_t mask;
	CPU_ZERO(&mask);
	CPU_SET((int)tmp /*+ (tmp >=6 ? 2 : 0)*/, &mask);
	assert(!pthread_setaffinity_np(pthread_self(), sizeof(mask), &mask));
	wthd[tmp].work(tmp);
}

CalcType ans[MAX_N];

struct AnsVal{
	CalcType cv;
	u32 id;
};

bool operator < (const AnsVal &A, const AnsVal &B)
{
	if(A.cv == B.cv)
		return A.id > B.id;
	return A.cv < B.cv;
}

priority_queue<AnsVal> Q;

bool cmp_vector_edge(const VectorEdge &A, const VectorEdge &B)
{
	return A.dis < B.dis;
}
int m = 0;

namespace remark{ // for cache hit

	bool vis[MAX_N];
	int remark[MAX_N], remark_cnt = 0;
	queue<int> Q;
	vector<VectorEdge> REM[MAX_N];
	int _redu[MAX_N];
	
	void dfs(int u)
	{
		if(vis[u])
			return;
		vis[u] = 1;
		remark[u] = ++remark[cnt];
		for(VectorEdge& edg: _G[u])
			dfs(edg.to);
	}
	
	void bfs()
	{
		/*
		for(int i = 1; i <= n; i++)
			dfs(i);
		*/
		for(int i = 1; i <= n; i++)
			if(!vis[i])
			{
				vis[i] = 1;
				Q.push(i);
				while(!Q.empty())
				{
					int now = Q.front();
					Q.pop();
					remark[now] = ++remark_cnt;
					for(VectorEdge& edg: _G[now])
					if(!vis[edg.to])
					{
						vis[edg.to] = 1;
						Q.push(edg.to);
					}
				}
			}
		for(int i = 1; i <= n; i++)
		{
			for(VectorEdge edg: _G[i])
			{
				edg.to = remark[edg.to];
				REM[remark[i]].push_back(edg);
			}
			_redu[remark[i]] = redu[i];
		}
		for(int i = 1; i <= n; i++)
			redu[i] = _redu[i];
	}

}

int main()
{
	double st = cur_time();
	FILE *input_file = freopen("test_data2.txt"/*"/data/test_data.txt"*/, "r", stdin);
	FILE *output_file = freopen("result.txt"/*"/projects/student/result.txt"*/, "w", stdout);
	
	type_switch = 1; // zip
	
	int u,v,w;
	while(~scanf("%d,%d,%d", &u, &v, &w))
	if(w > 0)
	{
		u = get_id(u);
		v = get_id(v);
		// add_edge(u, v, w);
		_G[u].push_back({v, (u16)w});
		//RG[u].push_back({v, (u16)w});
		if(w >= (1<<11))
			type_switch = 0;
		m++;
	}
	n = id_cnt;
	
	for(int i = 1; i <= 5000; i++)
		pre_div[i] = 1.0 / i;
	for(int i = 1; i <= n; i++)
		sort(_G[i].begin(), _G[i].end(), cmp_vector_edge);
		
	remark::bfs();
	
	pointer_switch = 1; // switch pointer of edge table
	for(int i = 1; i <= n; i++)
	if(remark::REM[i].size() >= MAX_D)
	{
		pointer_switch = 0;
		break;
	}
	if(type_switch == 0)
	{
		if(pointer_switch == 0)
		{
			int total_m = 0;
			for(int i = 1; i <= n; i++)
			{
				G1[i].begin = buffer1 + total_m;
				cd[i] = remark::REM[i].size();
				for(auto& edg: remark::REM[i])
				{
					rd[edg.to]++;
					buffer1[total_m++] = edg;
				}
				G1[i].end = buffer1 + total_m;
				_G[i].clear();
			}
		}
		else
		{
			for(int i = 1; i <= n; i++)
			{
				cd[i] = remark::REM[i].size();
				for(auto& edg: remark::REM[i])
				{
					rd[edg.to]++;
					buffer1[i * MAX_D + (++buffer1[i * MAX_D].to)] = edg;
				}
				_G[i].clear();
			}
		}
		for(int i = 1; i <= n; i++)
			for(VectorEdge *edg = Begin1(i); edg != End1(i); edg++)
				_G[edg->to].push_back({i, edg->dis});
	}
	else
	{
		if(pointer_switch == 0)
		{
			int total_m = 0;
			for(int i = 1; i <= n; i++)
			{
				G2[i].begin = buffer2 + total_m;
				cd[i] = remark::REM[i].size();
				for(auto& edg: remark::REM[i])
				{
					rd[edg.to]++;
					buffer2[total_m++] = ((u32)edg.dis << 21) + edg.to;
				}
				G2[i].end = buffer2 + total_m;
				_G[i].clear();
			}
		}
		else
		{
			for(int i = 1; i <= n; i++)
			{
				cd[i] = remark::REM[i].size();
				for(auto& edg: remark::REM[i])
				{
					rd[edg.to]++;
					buffer2[i * MAX_D + (++buffer2[i * MAX_D])] = ((u32)edg.dis << 21) + edg.to;
				}
				_G[i].clear();
			}
		}
		for(int i = 1; i <= n; i++)
			for(u32 *edg = Begin2(i); edg != End2(i); edg++)
				_G[(*edg)&Max_Weight].push_back({i, (u16)((*edg) >> 21)});
	}
		
	for(int i = 1; i <= n; i++)
		sort(_G[i].begin(), _G[i].end(), cmp_vector_edge);
	#ifdef DEBUG
	cerr << "鐐规暟: " << n << endl;
	cerr << "杈规暟: " << m << endl;
	#endif
	
	
		
	tarjan::n = n;
	for(int i = 1; i <= n; i++)
		NW::wt[i] = 1;
	
	for(int i = 1; i <= n; i++)
		tarjan::tarjan(i);
	
	int fucked_cnt = 0;
	
	for(int i = 1; i <= n; i++)
	{
		int u = NW::topl_sort[i];
		if(type_switch)
		{
			if(cd[u] == 1 && tarjan::dye[(*Begin2(u))&Max_Weight] != tarjan::dye[u])
			{
				MG[(*Begin2(u))&Max_Weight].push_back(u);
				NW::wt[(*Begin2(u))&Max_Weight] += NW::wt[u];
				NW::fucked[u] = 1;
				fucked_cnt++;
			}
		}
		else
		{
			if(cd[u] == 1 && tarjan::dye[Begin1(u)->to] != tarjan::dye[u])
			{
				MG[Begin1(u)->to].push_back(u);
				NW::wt[Begin1(u)->to] += NW::wt[u];
				NW::fucked[u] = 1;
				fucked_cnt++;
			}
		}
	}
	
	for(int i = 1; i <= n; i++)
	if(!NW::fucked[i])
	{
		missions.push({i, -tarjan::dye[i]});
		miq[i] = 1;
	}
	#ifdef DEBUG
	
	cerr << "寮鸿繛閫氬垎閲? " << tarjan::CN <<endl;
	cerr << "鍙紭鍖栫偣: " << fucked_cnt <<endl;
	cerr << "pre_stamp: " << cur_time() - st << endl;
	
	#endif
	pthread_t src[NThread]; void *thrd_ret;
	for(int i = 0; i < NThread; i++)
		pthread_create(&src[i], NULL, do_it, (void*)(1ull*i));
	for(int i = 0; i < NThread; i++)
	{
		pthread_join(src[i], &thrd_ret);
		for(int j = 1; j <= n; j++)
			ans[j] += wthd[i].ans[j];
	}
	
	#ifdef DEBUG
		cerr << wtf <<endl;
	#endif
	
	for(int i = 1; i <= n; i++)
		Q.push({ans[i], redu[i]});
	int ANS_NUM = min(n, 100);
	
	while(ANS_NUM--)
	{
		AnsVal now = Q.top();
		Q.pop();
		printf("%u,%.3lf\n", now.id, (double)now.cv);
	}
	
	return 0;
}
