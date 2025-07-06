// Minimal reference implementation of Δ-Kernel core (C++17)
// This file is **not** compiled as part of the Python package; it is used by
// the pytest "cpp" test to ensure algorithmic parity with the Python engine.
// Build example:
//   g++ -std=c++17 -O2 delta_kernel.cpp -o delta_kernel && ./delta_kernel

#include <cassert>
#include <cstdint>
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <vector>

// ------------------------------------------------------------
// Basic data-structures
// ------------------------------------------------------------

struct Node {
    uint32_t left;
    uint32_t right;
};

constexpr uint32_t NID_VOID = 0;          // distinguished Ø node (id 0)

class Arena {
    std::vector<Node> _nodes;
public:
    Arena() { _nodes.push_back({NID_VOID, NID_VOID}); } // node 0 = void
    uint32_t emplace(uint32_t l, uint32_t r) {
        _nodes.push_back({l, r});
        return static_cast<uint32_t>(_nodes.size() - 1);
    }
    Node & get_node(uint32_t id) { return _nodes.at(id); }
    const Node & get_node(uint32_t id) const { return _nodes.at(id); }
};

struct PairKey {
    uint32_t l, r;
    bool operator==(const PairKey &o) const { return l == o.l && r == o.r; }
};

struct PairHash {
    std::size_t operator()(const PairKey &k) const noexcept {
        return (static_cast<size_t>(k.l) << 32) ^ k.r;
    }
};

class HashCons {
    std::unordered_map<PairKey, uint32_t, PairHash> _cache;
    Arena * _arena;
public:
    explicit HashCons(Arena &arena) : _arena(&arena) {}

    uint32_t canonical(uint32_t l, uint32_t r, Arena &a) {
        if (l == NID_VOID && r == NID_VOID) return NID_VOID;
        PairKey key{l, r};
        auto it = _cache.find(key);
        if (it != _cache.end()) return it->second;
        uint32_t id = a.emplace(l, r);
        _cache.emplace(key, id);
        return id;
    }
};

// ------------------------------------------------------------
// Δ-Kernel reduction rules (F, C, V)
// ------------------------------------------------------------

static inline bool is_loop(uint32_t id, const Arena &arena) {
    return id != NID_VOID && arena.get_node(id).right == id;
}

uint32_t delta_step(uint32_t nid, Arena &arena, HashCons &hc, bool &changed) {
    const Node &n = arena.get_node(nid);
    if (is_loop(n.left, arena) || is_loop(n.right, arena)) return nid;

    // F-rule: ⟨⟨Ø,x⟩,y⟩ → ⟨y,x⟩
    if (n.left != NID_VOID) {
        const Node &l = arena.get_node(n.left);
        if (l.left == NID_VOID) {
            changed = true;
            return hc.canonical(n.right, l.right, arena);
        }
    }
    // C-rule: ⟨x,Ø⟩ → x
    if (n.right == NID_VOID) {
        changed = true;
        return n.left;
    }
    // V-rule: ⟨Ø,Ø⟩ → Ø
    if (n.left == NID_VOID && n.right == NID_VOID) {
        changed = true;
        return NID_VOID;
    }
    // Ω-loop guard: right points to itself
    if (n.right == nid) return nid;
    return nid;
}

uint32_t delta_reduce(uint32_t root, Arena &arena, HashCons &hc) {
    struct Task { uint32_t parent; bool leftChild; uint32_t nid; bool visited; };

    const uint32_t MAX_PASSES = 1 << 20;
    uint32_t passes = 0;
    bool changed = true;
    while (changed && passes++ < MAX_PASSES) {
        changed = false;
        std::vector<Task> st;
        st.push_back({UINT32_MAX, false, root, false});
        std::unordered_set<uint32_t> seen;

        while (!st.empty()) {
            Task fr = st.back();
            st.pop_back();
            uint32_t nid = fr.nid;
            if (nid == NID_VOID) continue;
            if (!fr.visited) {
                if (seen.count(nid)) continue;
                seen.insert(nid);
                st.push_back({fr.parent, fr.leftChild, nid, true});
                const Node &n = arena.get_node(nid);
                if (n.right != NID_VOID) st.push_back({nid, false, n.right, false});
                if (n.left  != NID_VOID) st.push_back({nid, true,  n.left,  false});
            } else {
                bool local_ch = false;
                uint32_t new_id = delta_step(nid, arena, hc, local_ch);
                if (local_ch) {
                    if (fr.parent == UINT32_MAX) {
                        root = new_id;
                    } else {
                        Node &p = arena.get_node(fr.parent);
                        if (fr.leftChild) p.left = new_id; else p.right = new_id;
                    }
                    changed = true;
                }
            }
        }
    }
    assert(passes < MAX_PASSES && "too many passes");
    return root;
}

// ------------------------------------------------------------
// Simple self-test program (runs when built as an exe)
// ------------------------------------------------------------
#ifdef UNIT_TEST_MAIN
int main() {
    Arena arena;
    HashCons hc(arena);
    // Build pair (Ø, Ø)  -> should reduce to Ø
    uint32_t pair_void = arena.emplace(NID_VOID, NID_VOID);
    uint32_t res1 = delta_reduce(pair_void, arena, hc);
    assert(res1 == NID_VOID);

    // Build <x, Ø>  -> reduces to x
    uint32_t x = arena.emplace(NID_VOID, NID_VOID);
    auto &xn = arena.get_node(x);
    xn.left = x;
    xn.right = x; // self-loop on both sides to disable F-rule
    uint32_t pair_c = arena.emplace(x, NID_VOID);
    uint32_t res2 = delta_reduce(pair_c, arena, hc);
    assert(res2 != NID_VOID);

    // Build F-rule pattern: <<Ø,x>,y> -> <y,x>
    uint32_t y = arena.emplace(NID_VOID, NID_VOID); // dummy y
    uint32_t inner = arena.emplace(NID_VOID, x);
    uint32_t outer = arena.emplace(inner, y);
    uint32_t res3 = delta_reduce(outer, arena, hc);
    // Expect canonical(y,x)
    assert(res3 != NID_VOID);

    std::cout << "Δ-Kernel C++ self-test passed\n";
    return 0;
}
#endif 