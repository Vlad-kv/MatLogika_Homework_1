#include <iostream>
#include <cstdlib>
#include <cstdio>
#include <vector>
#include <set>
#include <map>
using namespace std;

const char NEGATION[] = "!";
const char CONJUNCTION[] = "&";
const char DISJUNCTION[] = "|";
const char CONSEQUENCE[] = "->";

map<string, int> rang = {
			{NEGATION, 1},
			{CONJUNCTION, 2},
			{DISJUNCTION, 3},
			{CONSEQUENCE, 4}
		};

struct expr{
	expr *a[2];
	int rang;
	string val;
	
	expr(expr *c, string &val, expr *v, int rang) :
		rang(rang), val(val) {
		a[0] = c;
		a[1] = v;
	}
	
	expr(expr *c, const char *val, expr *v, int rang) :
		rang(rang), val(val) {
		a[0] = c;
		a[1] = v;
	}
	
	expr(expr *c, const char *val, expr *v) :
		rang (::rang[val]), val(val) {
		
		a[0] = c;
		a[1] = v;
	}
	
	expr(expr *c, string val, expr *v) :
		rang (::rang[val]), val(val) {
		
		a[0] = c;
		a[1] = v;
	}
	
	~expr() {
		if (a[0]) {
			delete a[0];
		}
		if (a[1]) {
			delete a[1];
		}
	}
};

size_t pos;

expr* get_expression(string &s);

bool is_poss_id_char(char c) {
	return ( (('A' <= c) && (c <= 'Z')) ||
			 (('0' <= c) && (c <= '9')) );
}

void next(string &s) {
	pos++;
	while (pos < s.length()) {
		if ((s[pos] == ' ') || (s[pos] == 9) || (s[pos] == 13) ) {
			pos++;
		} else {
			break;
		}
	}
}

expr* get_negation(string &s) {
	if (s[pos] == '(') {
		next(s);
		expr *res = get_expression(s);
		
		if (s[pos] != ')') {
			throw "Error";
		}
		next(s);
		return res;
	}
	if (s[pos] == '!') {
		next(s);
		return new expr(0, NEGATION, get_negation(s), 1);
	}
	if (! (('A' <= s[pos]) && (s[pos] <= 'Z')) ) {
		throw "Error";
	}
	string res;
	res.push_back(s[pos]);
	next(s);
	
	while ( is_poss_id_char(s[pos]) ) {
		res.push_back(s[pos]);
		next(s);
	}
	
	return new expr(0, res, 0, 0);
}

expr* get_conjunction(string &s) {
	expr *res = get_negation(s);
	
	if (s[pos] == '&') {
		next(s);
		
		res = new expr(res, CONJUNCTION, get_conjunction(s), 2);
	}
	return res;
}

expr* get_disjunction(string &s) {
	expr *res = get_conjunction(s);
	
	if (s[pos] == '|') {
		next(s);
		
		res = new expr(res, DISJUNCTION, get_disjunction(s), 3);
	}
	return res;
}

expr* get_expression(string &s) {
	expr *res = get_disjunction(s);
	
	if (s[pos] == '-') {
		next(s);
		if (s[pos] != '>') {
			throw "Error";
		}
		next(s);
		
		res = new expr(res, CONSEQUENCE, get_expression(s), 4);
	}
	return res;
}

expr* to_expr(string &s) {
	pos = -1;
	next(s);
	if (pos == s.length()) {
		return 0;
	}
	
	expr *res = get_expression(s);
	
	if (pos != s.length()) {
		throw "Error";
	}
	return res;
}

void to_string(expr *c, string &res, int last_rang, int pos) {
	if ((c->rang > last_rang) || ((c->rang == last_rang) && (pos == 0))) {
		res.push_back('(');
	}
	
	if (c->a[0]) {
		to_string(c->a[0], res, c->rang, 0);
	}
	res.append(c->val);
	
	if (c->a[1]) {
		to_string(c->a[1], res, c->rang, 1);
	}
	
	if ((c->rang > last_rang) || ((c->rang == last_rang) && (pos == 0))) {
		res.push_back(')');
	}
}

string to_string(expr *c) {
	string res;
	to_string(c, res, 1<<30, 1);
	return res;
}

vector<string> str_axioms = {
	"A->B->A",
	"(A->B)->(A->B->C)->(A->C)",
	"A->B->A&B",
	"A&B->A",
	"A&B->B",
	"A->A|B",
	"B->A|B",
	"(A->C)->(B->C)->(A|B->C)",
	"(A->B)->(A->!B)->!A",
	"!!A->A"
};

vector<expr*> expr_axioms;

void init() {
	for (auto &s : str_axioms) {
		expr_axioms.push_back(to_expr(s));
	}
}

map<char, string> disp;

bool compare(expr *ax, expr *c) {
	if (!c) {
		return 0;
	}
	
	if ((ax->val.length() == 1) && (is_poss_id_char(ax->val[0]))) {
		char v = ax->val[0];
		if (disp.find(v) == disp.end()) {
			disp.insert({v, to_string(c)});
		} else {
			if (disp[v] != to_string(c)) {
				return 1;
			}
		}
		return 0;
	}
	if (ax->val != c->val) {
		return 1;
	}
	if ( ( (ax->a[0] == 0) ^ (c->a[0] == 0) ) || 
		 ( (ax->a[1] == 0) ^ (c->a[1] == 0) ) ) {
		 	return 0;
	}
	
	for (int w = 0; w < 2; w++) {
		if (ax->a[w]) {
			if (compare(ax->a[w], c->a[w])) {
				return 1;
			}
		}
	}
	return 0;
}

int check_if_it_scheme_of_ax(expr *c) {
	for (size_t w = 0; w < expr_axioms.size(); w++) {
		disp.clear();
		if (!compare(expr_axioms[w], c)) {
			return w;
		}
	}
	return -1;
}
int check_if_it_scheme_of_ax(string &s) {
	expr *c = to_expr(s);
	int res = check_if_it_scheme_of_ax(c);
	delete c;
	return res;
}

vector<expr*> assumptions;
vector<string> original_assumptions;
map<string, int> map_of_assumptions;

expr *need_to_pove;
string original_need_to_prove;

vector<expr*> proofs;
vector<string> original_proofs;

map<string, int> existing_proofs;

multimap<string, pair<string, int> > poss_poss_m_p;
map<string, pair<int, int> > poss_m_p;

void global_check() {
	string assumption, str;
	getline(cin, str);
	size_t w;
	
	for (w = 0; w < str.length(); w++) {
		if (str[w] == ',') {
			original_assumptions.push_back(assumption);
			assumptions.push_back(to_expr(assumption));
			assumption.clear();
			continue;
		}
		if ((str[w] == '|') && (str[w + 1] == '-')) {
			expr *ass = to_expr(assumption);
			if (ass == 0) {
				w += 2;
				break;
			}
			
			original_assumptions.push_back(assumption);
			assumptions.push_back(ass);
			assumption.clear();
			
			w += 2;
			break;
		}
		assumption.push_back(str[w]);
	}
	original_need_to_prove = "";
	
	while (w < str.length()) {
		original_need_to_prove.push_back(str[w]);
		w++;
	}
	need_to_pove = to_expr(original_need_to_prove);
	
	while (!feof(stdin)) {
		getline(cin, str);
		
		if (str == "") {
			continue;
		}
		
		original_proofs.push_back(str);
		proofs.push_back(to_expr(str));
	}
	
	int c = 0;
	
	for (auto w : assumptions) {
		if (c) {
			cout << ",";
		}
		cout << to_string(w);
		
		c++;
		map_of_assumptions.insert({to_string(w), c});
	}
	cout << "|-" << to_string(need_to_pove) << "\n";
	
	int no = 1;
	
	for (size_t w = 0; w < proofs.size(); w++) {
		cout << "(" << no << ") " << to_string(proofs[w]) << " (";
		no++;
		
		str = to_string(proofs[w]);
		
		map<string, int>::iterator it;
		multimap<string, pair<string, int> >::iterator it2;
		
		{
			int c = check_if_it_scheme_of_ax(proofs[w]);
			if (c >= 0) {
				cout << "Сх. акс. " << c + 1 << ")\n";
				goto cont;
			}
			
			it = map_of_assumptions.find(str);
			if (it != map_of_assumptions.end()) {
				cout << "Предп. " << (*it).second << ")\n";
				goto cont;
			}
			
			map<string, pair<int, int> >::iterator it3;
			
			it3 = poss_m_p.find(str);
			if (it3 != poss_m_p.end()) {
				cout << "M.P. " << (*it3).second.first + 1 << ", ";
				cout << (*it3).second.second + 1 << ")\n";
				goto cont;
			}
			
			cout << "Не доказано)\n";
		}
		cont:
		
		if (proofs[w]->val == CONSEQUENCE) {
			string left_child = to_string(proofs[w]->a[0]);
			
			it = existing_proofs.find(left_child);
			if (it != existing_proofs.end()) {
				poss_m_p.insert(
								{to_string(proofs[w]->a[1]), 
									{(*it).second, w} }
								);
			} else {
				poss_poss_m_p.insert({left_child, 
										{to_string(proofs[w]->a[1]), w}
									  } );
			}
		}
		
		it2 = poss_poss_m_p.find(str);
		while (it2 != poss_poss_m_p.end()) {
			poss_m_p.insert({(*it2).second.first, {w, (*it2).second.second} });
			
			poss_poss_m_p.erase(it2);
			it2 = poss_poss_m_p.find(str);
		}
		
		existing_proofs.insert({str, w});
	}
}
/*
expr *gen_expr(expr *c, int w) {
	for (; w > 0; w--) {
		expr **c1 = &c;
		int e, r;
		
		while (1) {
			e = rand() % 2;
			if (((*c1)->a[e]) && ( !is_poss_id_char((*c1)->a[e]->val[0]) )) {
				c1 = &(*c1)->a[e];
			} else {
				e = e ^ 1;
				if (((*c1)->a[e]) && ( !is_poss_id_char((*c1)->a[e]->val[0]) )) {
					c1 = &(*c1)->a[e];
				} else {
					break;
				}
			}
		}
		
		string str;
		
		r = rand();
		
		if (r % 4 == 3) {
			*c1 = new expr(0, NEGATION, *c1);
			continue;
		}
		
		if (r % 4 == 0) {
			str = CONSEQUENCE;
		}
		if (r % 4 == 1) {
			str = DISJUNCTION;
		}
		if (r % 4 == 2) {
			str = CONJUNCTION;
		}
		
		string str2;
		str2.push_back('A' + rand() % 10);
		expr *v = new expr(0, str2, 0, 0);
		v = new expr(0, NEGATION, v);
		
		e = rand() % 2;
		
		if (e == 0) {
			*c1 = new expr(*c1, str, v );
		} else {
			*c1 = new expr(v , str, *c1);
		}
	}
	return c;
}

vector<string> gen_str;

void generate(int num, int size) {
	expr *main_expr = new expr(0, "A", 0, 0);
	main_expr = new expr(0, NEGATION, main_expr);
	
	main_expr = gen_expr(main_expr, size);
	
	for (int w = 0; w < num + 2; w++) {
		expr *start_expr = new expr(0, "A", 0, 0);
		start_expr = new expr(0, NEGATION, start_expr);
		
		gen_str.push_back(to_string(new expr(main_expr, CONSEQUENCE, gen_expr(start_expr, size)   ) ));
		
		delete start_expr;
	}
	
	cout << gen_str[0] << "," << gen_str[0] << " |-" << gen_str[0] << "\n";
	
	for (auto w : gen_str) {
		cout << w << "\n";
	}
	
}
*/
int main() {
	freopen("input.txt", "r", stdin);
	freopen("output.txt", "w", stdout);
	
	init();
	
    global_check();
    //generate(5000, 28);
    return 0;
}
