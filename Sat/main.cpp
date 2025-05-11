#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <unordered_map>
#include <unordered_set>
#include <set>
#include <chrono>
#include <algorithm>
#include <iomanip>

using namespace std;
using namespace std::chrono;

typedef vector<int> Clause;
typedef vector<Clause> CNF;

CNF parseDIMACS(const string& filename, int& numVars) {
    CNF cnf;
    ifstream infile(filename);
    string line;
    while (getline(infile, line)) {
        if (line.empty() || line[0] == 'c') continue;
        if (line[0] == 'p') {
            istringstream iss(line);
            string tmp;
            int numClauses;
            iss >> tmp >> tmp >> numVars >> numClauses;
        } else {
            istringstream iss(line);
            Clause clause;
            int lit;
            while (iss >> lit && lit != 0) clause.push_back(lit);
            cnf.push_back(clause);
        }
    }
    return cnf;
}

bool resolution(const CNF& cnf) {
    using ClauseSet = set<int>;
    set<ClauseSet> clauseSet;
    for (const auto& clause : cnf)
        clauseSet.insert(ClauseSet(clause.begin(), clause.end()));

    set<pair<ClauseSet, ClauseSet>> resolvedPairs;
    int iteration = 0;
    size_t maxClauseSize = 0;
    const size_t CLAUSE_LIMIT = 1500;

    while (true) {
        iteration++;
        cout << "[RES] Iteration " << iteration
             << " | Clause set size: " << clauseSet.size() << endl;

        vector<ClauseSet> clauses(clauseSet.begin(), clauseSet.end());
        bool added = false;

        for (size_t i = 0; i < clauses.size(); ++i) {
            for (size_t j = i + 1; j < clauses.size(); ++j) {
                const auto& c1 = clauses[i];
                const auto& c2 = clauses[j];

                if (resolvedPairs.count({c1, c2}) || resolvedPairs.count({c2, c1})) continue;
                resolvedPairs.insert({c1, c2});

                for (int lit : c1) {
                    if (c2.count(-lit)) {
                        ClauseSet resolvent;
                        for (int l : c1) if (l != lit) resolvent.insert(l);
                        for (int l : c2) if (l != -lit) resolvent.insert(l);

                        bool tautology = false;
                        for (int l : resolvent)
                            if (resolvent.count(-l)) {
                                tautology = true;
                                break;
                            }

                        if (tautology) continue;

                        if (resolvent.empty()) {
                            cout << "[RES] Derived empty clause — UNSAT.\n";
                            return false;
                        }

                        if (!clauseSet.count(resolvent)) {
                            clauseSet.insert(resolvent);
                            maxClauseSize = max(maxClauseSize, resolvent.size());
                            added = true;
                        }
                    }
                }
            }
        }

        if (!added) {
            cout << "[RES] No new clauses. Terminating.\n";
            break;
        }

        if (clauseSet.size() > CLAUSE_LIMIT) {
            cout << "[RES] Aborted: clause set exceeded " << CLAUSE_LIMIT << " clauses.\n";
            return false;
        }
    }

    cout << "[RES] Finished. Max clause size: " << maxClauseSize << endl;
    return true;
}

bool dp(CNF cnf, int numVars) {
    static int dpDepth = 0;
    ++dpDepth;

    cout << "[DP depth " << dpDepth << "] Clauses: " << cnf.size() << endl;

    while (true) {
        bool changed = false;

        unordered_map<int, int> literalCount;
        for (const auto& clause : cnf)
            for (int lit : clause)
                literalCount[lit]++;

        set<int> pureLiterals;
        for (const auto& [lit, _] : literalCount)
            if (!literalCount.count(-lit))
                pureLiterals.insert(lit);

        if (!pureLiterals.empty()) {
            cout << "[DP] Pure literals removed: ";
            for (int lit : pureLiterals) cout << lit << " ";
            cout << endl;

            cnf.erase(remove_if(cnf.begin(), cnf.end(), [&](const Clause& c) {
                return any_of(c.begin(), c.end(), [&](int l) { return pureLiterals.count(l); });
            }), cnf.end());
            changed = true;
        }

        vector<int> unitLits;
        for (const auto& clause : cnf)
            if (clause.size() == 1)
                unitLits.push_back(clause[0]);

        if (!unitLits.empty()) {
            cout << "[DP] Unit clauses propagated: ";
            for (int lit : unitLits) cout << lit << " ";
            cout << endl;

            for (int unit : unitLits) {
                cnf.erase(remove_if(cnf.begin(), cnf.end(), [&](const Clause& c) {
                    return find(c.begin(), c.end(), unit) != c.end();
                }), cnf.end());
                for (auto& clause : cnf)
                    clause.erase(remove(clause.begin(), clause.end(), -unit), clause.end());
            }
            changed = true;
        }

        if (!changed) break;
    }

    if (any_of(cnf.begin(), cnf.end(), [](const Clause& c) { return c.empty(); })) {
        cout << "[DP] Empty clause found — UNSAT.\n";
        --dpDepth;
        return false;
    }

    if (cnf.empty()) {
        cout << "[DP] CNF empty — SAT.\n";
        --dpDepth;
        return true;
    }

    unordered_map<int, int> freq;
    for (const auto& clause : cnf)
        for (int lit : clause)
            freq[lit]++;

    int bestLit = 0, maxFreq = 0;
    for (const auto& [lit, count] : freq)
        if (count > maxFreq) bestLit = lit, maxFreq = count;

    cout << "[DP] Branching on literal " << bestLit << "\n";

    CNF posCnf, negCnf;
    for (auto& clause : cnf) {
        Clause c1 = clause, c2 = clause;
        c1.erase(remove(c1.begin(), c1.end(), -bestLit), c1.end());
        c2.erase(remove(c2.begin(), c2.end(), bestLit), c2.end());
        if (!count(clause.begin(), clause.end(), bestLit)) posCnf.push_back(c1);
        if (!count(clause.begin(), clause.end(), -bestLit)) negCnf.push_back(c2);
    }

    bool result = dp(posCnf, numVars) || dp(negCnf, numVars);
    --dpDepth;
    return result;
}

bool dpll(const CNF& cnf) {
    static int callDepth = 0;
    ++callDepth;

    cout << "[DPLL Depth: " << callDepth << "] Clauses: " << cnf.size() << endl;

    if (cnf.empty()) {
        cout << "[DPLL] Returning TRUE (empty CNF)\n";
        --callDepth;
        return true;
    }

    if (any_of(cnf.begin(), cnf.end(), [](const Clause& c){ return c.empty(); })) {
        cout << "[DPLL] Returning FALSE (empty clause found)\n";
        --callDepth;
        return false;
    }

    for (const Clause& clause : cnf) {
        if (clause.size() == 1) {
            int unit = clause[0];
            CNF newCnf;
            for (const Clause& c : cnf) {
                if (find(c.begin(), c.end(), unit) != c.end()) continue;
                Clause newClause;
                for (int lit : c) if (lit != -unit) newClause.push_back(lit);
                newCnf.push_back(newClause);
            }
            bool result = dpll(newCnf);
            --callDepth;
            return result;
        }
    }

    unordered_map<int, int> freq;
    for (const Clause& clause : cnf)
        for (int lit : clause) freq[lit]++;

    int bestLit = 0, maxCount = 0;
    for (const auto& [lit, count] : freq)
        if (count > maxCount) bestLit = lit, maxCount = count;

    CNF posCnf, negCnf;
    for (const Clause& clause : cnf) {
        if (find(clause.begin(), clause.end(), bestLit) != clause.end()) continue;
        Clause posClause;
        for (int lit : clause) if (lit != -bestLit) posClause.push_back(lit);
        posCnf.push_back(posClause);
    }
    for (const Clause& clause : cnf) {
        if (find(clause.begin(), clause.end(), -bestLit) != clause.end()) continue;
        Clause negClause;
        for (int lit : clause) if (lit != bestLit) negClause.push_back(lit);
        negCnf.push_back(negClause);
    }

    bool result = dpll(posCnf) || dpll(negCnf);
    --callDepth;
    return result;
}

template <typename Func>
pair<bool, double> runWithTime(Func f) {
    auto start = high_resolution_clock::now();
    bool result = f();
    auto stop = high_resolution_clock::now();
    double duration = duration_cast<microseconds>(stop - start).count() /1000.0;
    return {result, duration};
}

void generateCNF(const string& filename, int vars, int clauses) {
    ofstream out(filename);
    out << "p cnf " << vars << " " << clauses << "\n";
    srand(vars * 1000 + clauses);
    for (int i = 0; i < clauses; ++i) {
        for (int j = 0; j < 3; ++j) {
            int var = rand() % vars + 1;
            int sign = rand() % 2 ? 1 : -1;
            out << sign * var << " ";
        }
        out << "0\n";
    }
}

int main() {
    vector<pair<int, int>> testCases = {
        {25, 100},{50,200},{75,300},{100,400}, {125,500},{150,600},{175,700}
    };
    ofstream csv("benchmark.csv");
    csv << "Clauses | Vars | ResTime(ms) | DPTime(ms) | DPLLTime(ms)\n";

    for (auto [vars, clauses] : testCases) {
        string inputFile = "temp.cnf";
        generateCNF(inputFile, vars, clauses);

        int numVars;
        CNF problem = parseDIMACS(inputFile, numVars);

        auto [resResult, resTime] = runWithTime([&]() { return resolution(problem); });
        auto [dpResult, dpTime] = runWithTime([&]() { return dp(problem, numVars); });
        auto [dpllResult, dpllTime] = runWithTime([&]() { return dpll(problem); });

        csv << clauses << " | "
            << vars << " | "
            << fixed << setprecision(3)
            << resTime << " | "
            << dpTime << " | "
            << dpllTime << "\n";

        cout << "Benchmark completed for " << vars << " vars, " << clauses << " clauses.\n";
    }

    cout << "All results written to benchmark.csv";
    return 0;
}