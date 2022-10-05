#include<bits/stdc++.h>
using namespace std;

typedef long long type;

// Public constants
// q > 3Np
// p > 256, the ASCII extended table
// N, q, p, prime
const type N = 23, p = 257, q = 17737, INF = N * 100;

// Constante necessária a se discutir
const int d = N / 2;

string original_message = "#1 - Integrantes: Davi + Pietro + Barbosa\n#2 - Professor responsavel: Xexeo";
map<char, int> char_to_int;
map<int, char> int_to_char;

mt19937_64 llrand((int) chrono::steady_clock::now().time_since_epoch().count());

struct polynomial{
	vector<type> coef;
	
	polynomial(vector<type> _coef = {}) : coef(_coef) {}
	
	type degree(){
		if(coef.empty()) return -INF;
		return coef.size() - 1;
	}
	
	bool operator !=(polynomial o){
		if(coef.size() != o.coef.size())
			return true;
		for(int i = 0; i < coef.size(); i++)
			if(coef[i] != o.coef[i])
				return true;
		return false;
	}
	
	bool operator ==(polynomial o){
		return !((*this) != o);
	}
	
	void resize(size_t new_size){
		size_t old_size = coef.size();
		coef.resize(new_size);
		for(size_t i = old_size; i < new_size; i++)
			coef[i] = 0;
	}
	
	type back(){
		return coef.back();
	}
	
	size_t size(){
		return coef.size();
	}
	
	bool empty(){
		return coef.empty();
	}
	
	void pop_back(){
		coef.pop_back();
	}
	
	type& operator[](size_t id){
		return coef[id];
	}
};

// Public base
polynomial base;

struct key{
	// Private keys
	polynomial f, g, fp, fq;
	
	// Public key
	polynomial h;
	
	key(){}
};

void print(polynomial a){
	bool first = true;
	if(a.empty())
		cout << "0";
	for(int i = a.size() - 1; i >= 0; i--){
		if(a[i] == 0)
			continue;
		if(first){
			if(i == 0)
				cout <<  a[i];
			else if(abs(a[i]) != 1)
				cout << a[i] << "*x";
			else if(a[i] == -1)
				cout << "-x";
			else
				cout << "x";
			if(i > 1)
				cout << "^" << i;
			first = false;
		}
		else{
			if(a[i] > 0)
				cout << " + ";
			else
				cout << " - ";
			if(i == 0)
				cout << abs(a[i]);
			else{
				if(abs(a[i]) != 1)
					cout << abs(a[i]) << "*";
				cout << "x";
				if(i > 1)
					cout << "^" << i;
			}
		}
	}
	cout << endl;
}

polynomial add(polynomial a, polynomial b, type mod){
	polynomial r;
	r.resize(max(a.size(), b.size()));
	for(size_t i = 0; i < r.size(); i++){
		if(i < a.size())
			r[i] = a[i];
		if(i < b.size())
			r[i] += b[i];
		r[i] %= mod;
	}
	while(!r.empty() && r.back() == 0)
		r.pop_back();
	return r;
}

polynomial sub(polynomial a, polynomial b, type mod){
	polynomial r;
	r.resize(max(a.size(), b.size()));
	for(size_t i = 0; i < r.size(); i++){
		if(i < a.size())
			r[i] = a[i];
		if(i < b.size())
			r[i] -= b[i];
		r[i] %= mod;
	}
	while(!r.empty() && r.back() == 0)
		r.pop_back();
	return r;
}

polynomial multiply(polynomial a, polynomial b, type mod){
	polynomial r;
	if(a.degree() + b.degree() >= 0)
		r.resize(a.degree() + b.degree() + 1);
	for(size_t i = 0; i < a.size(); i++)
		for(size_t j = 0; j < b.size(); j++)
			r[i + j] = (r[i + j] + a[i] * b[j]) % mod;
	while(!r.empty() && r.back() == 0)
		r.pop_back();
	return r;
}

type phi(type mod){
	type ans = mod;
	for(type i = 2; i * i <= mod; i++){
		if(mod % i == 0) ans -= ans / i;
		while(mod % i == 0) mod /= i;
	}
	if(mod != 1) ans -= ans / mod;
	return ans;
}

type fexp(type x, type y, type mod){
	type r = 1;
	while(y){
		if(y & 1)
			r = r * x % mod;
		x = x * x % mod;
		y >>= 1;
	}
	return (r + mod) % mod;
}

type inv(type x, type mod){
	return fexp(x, phi(mod) - 1, mod);
}

polynomial poly_floor(polynomial a, polynomial b, type mod){
	polynomial r;
	if(b.degree() == -INF){
		cout << "Divisão por zero\n";
		return r;
	}
	if(b.degree() > a.degree())
		return r;
	r.resize(a.degree() - b.degree() + 1);
	while(a.degree() >= b.degree()){
		type mult = (a.back() * inv(b.back(), mod) % mod);
		r[a.degree() - b.degree()] = mult;
		for(int i = 0; i <= b.degree(); i++)
			a[a.degree() - b.degree() + i] = (a[a.degree() - b.degree() + i] - b[i] * mult) % mod;
		while(!a.empty() && a.back() == 0)
			a.pop_back();
	}
	while(!r.empty() && r.back() == 0)
		r.pop_back();
	return r;
}

polynomial remainder(polynomial a, polynomial b, type mod){
	polynomial r;
	if(b.degree() == -INF)
		r = a;
	else
		r = sub(a, multiply(b, poly_floor(a, b, mod), mod), mod);
	return r;
}

int myrandom (int i) { return llrand()%i;}

polynomial random_key(int qp, int qn){
	polynomial key;
	key.coef.resize(N);
	for(int i = 0; i < qp; i++)
		key.coef[i] = 1;
	for(int i = 0; i < qn; i++)
		key.coef[i + qp] = -1;
	random_shuffle(key.coef.begin(), key.coef.end(), myrandom);
	while(!key.empty() && key.back() == 0)
		key.pop_back();
	return key;
}

polynomial gcd(polynomial a, polynomial b, polynomial &x, polynomial &y, type mod){
	if(b.degree() >= 0){
		polynomial r = gcd(b, remainder(a, b, mod), y, x, mod);
		y = sub(y, multiply(x, poly_floor(a, b, mod), mod), mod);
		return r;
	}
	else{
		x = polynomial({1});
		y = polynomial();
		return a;
	}
}

key generate_keys(){
	key r;
	polynomial aux;
	r.f = random_key(d + 1, d);
	while(gcd(r.f, base, r.fp, aux, p) != polynomial({1}) || gcd(r.f, base, r.fq, aux, q) != polynomial({1}))
		r.f = random_key(d + 1, d);
	r.g = random_key(d, d);
	r.h = remainder(multiply(r.fq, r.g, q), base, q);
	return r;
}

polynomial msg_to_poly(string message){
	polynomial m;
	m.resize(message.size());
	for(int i = 0; i < message.size(); i++)
		m[i] = char_to_int[message[i]];
	return m;
}

polynomial encrypt(string message, polynomial h){
	polynomial r = random_key(d, d);
	polynomial m = msg_to_poly(message);
	cout << "m = ";
	print(m);
	cout << "r = ";
	print(r);
	for(type &i : r.coef)
		i = i * p % q;
	while(!r.empty() && r.back() == 0)
		r.pop_back();
	return remainder(add(m, multiply(r, h, q), q), base, q);
}

polynomial decrypt(polynomial e, key k){
	polynomial a = remainder(multiply(k.f, e, q), base, q);
	for(type &i : a.coef){
		if(i < -q / 2) i += q;
		if(i > q / 2) i -= q;
	}
	return remainder(multiply(k.fp, a, p), base, p);
}

string poly_to_msg(polynomial d){
	string msg;
	for(int i = 0; i < d.size(); i++){
		if(d[i] < -p / 2)
			d[i] += p;
		if(d[i] > p / 2)
			d[i] -= p;
		msg += int_to_char[d[i]];
	}
	return msg;
}

int main(){
	for(int i = 0; i < 128; i++){
		char_to_int[char(i)] = -128 + i;
		int_to_char[-128 + i] = char(i);
	}
	for(int i = 128; i < 256; i++){
		char_to_int[char(i)] = i - 127;
		int_to_char[i - 127] = char(i);
	}
	
	base.coef.resize(N + 1);
	base.coef[N] = 1;
	base.coef[0] = -1;
	cout << "Base = ";
	print(base);
	
	key k = generate_keys();
	cout << "N = " << N << ", p = " << p << ", q = " << q << endl;
	cout << "f = ";
	print(k.f);
	cout << "fp = ";
	print(k.fp);
	cout << "fq = ";
	print(k.fq);
	cout << "g = ";
	print(k.g);
	cout << "h = ";
	print(k.h);
	
	cout << "\nOriginal message:\n" << original_message << endl;
	string decrypt_message;
	for(int i = 0; i < original_message.size(); i += N){
		string message = original_message.substr(i, min((int)N, (int)original_message.size() - i));
		cout << "\nPart #" << (i + N) / N << ":\n" << message << "\n";
		polynomial e = encrypt(message, k.h);
		cout << "e = ";
		print(e);
		
		polynomial d = decrypt(e, k);
		cout << "d = ";
		print(d);
		decrypt_message += poly_to_msg(d);
	}
	
	cout << "Original message:\n" << decrypt_message << endl;
	return 0;
}
