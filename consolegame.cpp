// consolegame.cpp : Defines the entry point for the console application.
//

#include "stdafx.h"
#include <functional>
#include <assert.h>

//#define NO_OPTIMIZATION

typedef uint8_t Square;
typedef unsigned Safety;
const Square Out = 4;
const Square Empty = 0;
const Square White = 1;
const Square Black = 2;
const int simple_sum[] = { 0,1,-1,0 };
const int empty_sum[] = { 1,0,0,0 };

typedef Square BoardArray[100];
typedef Square BoardLineArray[10];
const int NUMDIR = 8;
const int Directions[] = { 11,9,-11,-9,1,-1,10,-10,0 };
const int LineDirections[] = { 1,-1,0 };

struct ValTriple { int pos; int dir; int len; };
Safety *safety[8];
const ValTriple Valuations[] =
{
	{ 81,11,1 },{ 81,1,8 },
	{ 71,11,2 },{ 71,1,8 },
	{ 61,11,3 },{ 61,1,8 },
	{ 51,11,4 },{ 51,1,8 },
	{ 41,11,5 },{ 41,1,8 },
	{ 31,11,6 },{ 31,1,8 },
	{ 21,11,7 },{ 21,1,8 },
	{ 11,11,8 },{ 11,1,8 },{ 11,9,1 },{ 11,10,8 },
	{ 12,11,7 },{ 12,9,2 },{ 12,10,8 },
	{ 13,11,6 },{ 13,9,3 },{ 13,10,8 },
	{ 14,11,5 },{ 14,9,4 },{ 14,10,8 },
	{ 15,11,4 },{ 15,9,5 },{ 15,10,8 },
	{ 16,11,3 },{ 16,9,6 },{ 16,10,8 },
	{ 17,11,2 },{ 17,9,7 },{ 17,10,8 },
	{ 18,11,1 },{ 18,9,8 },{ 18,10,8 },
	{ 28,9,7 },
	{ 38,9,6 },
	{ 48,9,5 },
	{ 58,9,4 },
	{ 68,9,3 },
	{ 78,9,2 },
	{ 88,9,1 },
	{ 0,0,0 }
};

Safety compress_a[256];
Safety compress_b[256];
void init_compress()
{
	for (int c=0;c<256;++c)
		compress_a[c] = (c & 3) + ((((c & 0xc) * 12288) + ((c & 0x30) * 9216) 
			+ ((c & 0xc0) * 6912)) >> 14);

	for (int c = 256;c < 65536;c+=256)
		compress_b[c>>8] = ((((c & 0x300) * 5184)
			+ ((c & 0xc00) * 3888) + ((c & 0x3000) * 2916) + ((c & 0xc000) * 2187)) >> 14);
}
//reduce cache pressure by converting base 3 index to compressed form
inline Safety compress3(int c)
{
	return compress_a[c&255]+compress_b[c>>8];
}


/*x,0,x,x,x,x,x,x,x,2,4,6*/
const int shifts[] = { -1,0,-1,-1,-1,-1,-1,-1,-1,2,4,6 };
typedef int ValuationArray[100];
ValuationArray aValuationArray;

Square undo_buffer_array[64 * 10];
Square *undo_buffer = &undo_buffer_array[0];

inline Square other_color(Square c) { return (Black + White) ^ c; }

//note white is positive, black negative
//add number of pieces to this
int Values[256];
const int values_by_color[] = { -64,-32,-16,-8,0,8,16,32,64 };
void initValues()
{
	for (int i = 0;i < 256;++i) {
		int count_black = 0;
		int count_white = 0;
		int count_ambig = 0;
		for (int p = 0;p < 4;++p) {
			int at = (i >> (p + p)) & 3;
			switch (at) {
			case 1:
				if (count_black) {
					--count_black;
					++count_ambig;
				}
				else ++count_white;
				break;
			case 2:
				if (count_white) {
					--count_white;
					++count_ambig;
				}
				else ++count_black;
				break;
			case 3:
				++count_ambig;
			}

		}
		Values[i] = values_by_color[count_white - count_black + 4] >> count_ambig;
	}
}

bool move(Square *&undo, int pos, Square color, Square *board, const int *directions, bool check = false)
{
	if (board[pos] != Empty) return false;
	Square other = other_color(color);
	Square *u = undo;
	Square *r = &board[pos];
	for (int d = 0;directions[d];++d) {
		int dir = directions[d];
		if (r[dir] == other) {
			Square * o = &r[dir];
			while (o[dir] == other) o += dir;
			if (o[dir] == color) {
				if (check) return true;
				do {
					*u++ = o - board;
					*o = color;
					o -= dir;
				} while (o != r);
			}
		}
	}
	if (u != undo) {
		*u++ = u - undo;
		*u++ = pos;
		board[pos] = color;
		undo = u;
		return true;
	}
	return false;
}
void undo(Square *&undo, Square *board)
{
	if (undo_buffer == &undo_buffer_array[0]) return;
	Square *u = undo;
	board[*--u] = Empty;
	int num = *--u;
	while (num-- > 0) {
		board[*--u] ^= (White + Black);
	}
	undo = u;
}

static int blacklru[64] = {
	11,18,81,88,
	13,16,38,68,86,83,61,31,
	14,15,48,58,84,85,41,51,
	33,34,35,36,43,44,45,46,53,54,55,56,63,64,65,66,
	23,24,25,26,37,47,57,67,73,74,75,76,32,42,52,62,
	12,21,17,28,78,87,82,71,
	22,27,77,72
};
static int whitelru[64] = {
	11,18,81,88,
	13,16,38,68,86,83,61,31,
	14,15,48,58,84,85,41,51,
	33,34,35,36,43,44,45,46,53,54,55,56,63,64,65,66,
	23,24,25,26,37,47,57,67,73,74,75,76,32,42,52,62,
	12,21,17,28,78,87,82,71,
	22,27,77,72
};


class Board {
public:
	Board() {
		for (int i = 0;i < 100;++i) board[i] = Empty;
		for (int i = 0;i < 9;++i) {
			board[90 - i * 10] = board[99 - i] = board[9 + i * 10] = board[i] = Out;
		}
		board[44] = board[55] = White;
		board[45] = board[54] = Black;
	}
	bool move(Square *&undo, int pos, Square color, bool check = false) {
		return ::move(undo, pos, color, board, Directions, check);
	}
	void undo(Square *&undo, Square *board)
	{
		::undo(undo, board);
	}
	BoardArray board;
	void print()
	{
		int b = 0, w = 0;
		const char *p = ".*Ox#";
		printf("     1 2 3 4 5 6 7 8\n");
		for (int i = 0;i < 100;++i) {
			if (i % 10 == 0) {
				if (i == 0 || i == 90) printf("   ");
				else printf(" %i ", i / 10);
			}
			putchar(p[board[i]]);putchar(' ');
			if (board[i] == Black) ++b;
			else if (board[i] == White) ++w;
			if (i % 10 == 9) putchar('\n');
		}
		printf("%i black pieces, %i white pieces\n", b, w);
	}

	int alphabeta(int &move_at, int depth, int alpha, int beta, Square color, Square root_color, bool use_move_count);
	int endgame_alphabeta(int &move_at, int depth, int alpha, int beta, Square color, Square root_color, bool passed = false);


#ifdef NO_OPTIMIZATION
	bool next_move(int &move_number, int &move_at, Square color)
	{
		if (move_number > 63) return false;
		int at = move_at;
		do {
			if (move_number == 64) return false;
			at = (move_number & 7) + 11 + (move_number >> 3) * 10;
			++move_number;
		} while (!move(undo_buffer, at, color));
		move_at = at;
		return true;
	}
	void killer(int move_number, Square color) {}
#else
	void killer2(int move_number, Square color)
	{
		if (move_number == 0) return;
		int *lru;
		if (color == White)lru = whitelru;
		else lru = blacklru;
		int at = lru[move_number];
		for (int i = move_number - 1;i >= 0;--i) lru[i + 1] = lru[i];
		lru[0] = at;
	}
	void killer(int move_number, Square color)
	{
		if (move_number <= 1) return;
		int *lru;
		if (color == White)lru = whitelru;
		else lru = blacklru;
		int at = lru[move_number];
		int a0 = lru[0];
		int a1 = lru[move_number >> 1];

		lru[0] = at;
		lru[move_number >> 1] = a0;
		lru[move_number] = a1;
	}
	bool next_move(int &move_number, int &move_at, Square color)
	{
		if (move_number > 63) return false;
		int at;
		do {
			if (move_number == 64) return false;
			//at = (move_number >> 3) * 10 + (move_number & 7) + 11;
			//++move_number;
			if (color == White)at = whitelru[move_number++];
			else at = blacklru[move_number++];
		} while (!move(undo_buffer, at, color));
		move_at = at;
		return true;
	}
#endif
	int find_move(int depth, Square color, bool use_move_count);
	bool can_move(Square color)
	{
		for (int p = 11;p <= 88;++p) if (move(undo_buffer, p, color, true)) return true;
		return false;
	}
	int forced_move(int & move_at, Square color)
	{
		int moves = 0;
		move_at = 0;
		for (int p = 11;p <= 88;++p) {
			if (move(undo_buffer, p, color, true)) {
				move_at = p;
				if (++moves == 2) return false;
			}
		}
		return true;
	}
	int count_moves(int & move_at, Square color)
	{
		int moves = 0;
		move_at = 0;
		for (int p = 11;p <= 88;++p) {
			if (move(undo_buffer, p, color, true)) {
				move_at = p;
				++moves;
			}
		}
		return moves;
	}

	void input(Square color, const char *command = NULL)
	{
		do {
			char buf[20];
			print();
			if (color == White) fputs("White's", stdout);
			else fputs("Black's", stdout);
			fputs(" move (p for pass, u undo, a[n] auto, b[n] alt auto):", stdout);
			if (command) strcpy(buf, command);
			else fgets(buf, sizeof(buf) - 1, stdin);
			int i = -1;
			sscanf(buf, "%i", &i);
			if (buf[0] == 'p') return;

			if (buf[0] == 'a') {
				int m = find_move(buf[1] - '0', color, false);
				printf("move at %i\n", m);
				if (!move(undo_buffer, m, color)) {
					printf("pass.\n");
				}
				return;

			}
			if (buf[0] == 'b') {
				int m = find_move(buf[1] - '0', color, true);
				printf("move at %i\n", m);
				if (!move(undo_buffer, m, color)) {
					printf("pass.\n");
				}
				return;

			}

			if (buf[0] == 'u') {
				undo(undo_buffer, board);

				return;
			}
			if (i < 11 || i>99 || !move(undo_buffer, i, color)) {
				printf("bad move.\n");
			}
			else return;
		} while (true);
	}
};

//note is singleton
class Valuator
{
public:

	BoardLineArray board;

	int CalcSafety(int len, int c)//note board is one input, undo_buffer another
	{
		for (int p = 0;p < len;++p) {
			for (int color = White; color <= Black;++color) {
				if (board[p + 1] == Empty) {
					if (move(undo_buffer, p + 1, color)) {
						for (int s = 0;s < len;++s) c |= board[s + 1] << (s + s);
						c |= CalcSafety(len, c);
						undo(undo_buffer);
					}
					else {
						board[p + 1] = color;
						c |= color << (p + p);
						c |= CalcSafety(len, c);
						board[p + 1] = Empty;
					}
				}
			}
		}
		return c;
	}
	void CalcValuate(int len)
	{
		board[len + 1] = Out;
		for (int c = 0;c < 1 << (len + len);++c) {
			for (int i = 0;i < len;++i) {
				int mask = 3 << (i + i);
				if ((c&mask) == mask) goto cont_c;
				board[i + 1] = (c&mask) >> (i + i);
			}
			//the board line now has every starting position
			//do every possible move from this position, and or the results
			//every square that isn't 3 is safe.
			//calc safety[i-1][c]
			safety[len - 1][compress3(c)] = CalcSafety(len, c);
			//			safety[len - 1][c] = (((c & 0xaaaaaaaa) >> 1) | ((c & 0x55555555) << 1) | c) & CalcSafety(len, c);
			//printf("safety len=%i[%x]=%x\n",len,c,safety[len - 1][c]);
		cont_c:;
		}
	}

	Valuator() {
		init_compress();
		int len = 4;
		for (int i = 1;i <= 8;++i) {
			safety[i - 1] = new Safety[len];
			memset(safety[i - 1], 0, len * sizeof(safety[i - 1][0]));
			len = len * 4;
		}
		for (int i = 0;i < 10;++i) board[i] = Empty;
		board[0] = board[9] = Out;
		for (int i = 8; i >= 1;--i) CalcValuate(i);
		initValues();

		/*
		len = 4;
		for (int i = 1;i <= 8;++i) {
		printf("safety of length %i\n", len);
		for (int j = 0;j < len;++j) {
		if (safety[i - 1][j]) fprintf(stderr,"%8x ",safety[i - 1][j]);
		}
		len = len * 4;
		}
		*/
	}
	~Valuator() {
		for (int i = 1;i <= 8;++i) delete[] safety[i - 1];
	}
	bool move(Square *&undo, int pos, Square color, bool check = false) {
		return ::move(undo, pos, color, board, LineDirections, check);

	}
	void undo(Square *&undo)
	{
		::undo(undo, board);
	}

	int find_empty(BoardArray in)
	{
		int sum = 0;
		for (int i = 11;i <= 88;++i) sum += empty_sum[in[i]];
		return sum;
	}
	int find_simple_value(BoardArray in, Square root_color)
	{
		int sum = 0;
		for (int i = 11;i <= 88;++i) sum += simple_sum[in[i]];
		if (root_color == Black) return -sum;
		return sum;
	}
	int find_value(BoardArray in, Square root_color, bool use_move_count, bool display)
	{
		for (int i = 11;i <= 88;++i) aValuationArray[i] = 0;
		for (int i = 0;Valuations[i].pos; ++i) {
			int c = 0;
			for (int j = Valuations[i].pos, k = 1;k <= Valuations[i].len;++k, j = j + Valuations[i].dir) {
				c = (c << 2) + in[j];

			}
			c = safety[Valuations[i].len - 1][compress3(c)];
			int s = shifts[Valuations[i].dir];
			assert(s >= 0);
			for (int j = Valuations[i].pos + Valuations[i].dir*(Valuations[i].len - 1), k = 1;k <= Valuations[i].len;++k, j = j - Valuations[i].dir) {
				aValuationArray[j] |= (c & 3) << s;
				c >>= 2;
			}
		}
		//at this point I should have a board of safety values to flatten
		int sum = 0;
		static int intrans[] = { 0,2,-2,0,0 };
		for (int i = 11;i <= 88;++i) sum += Values[aValuationArray[i]] + intrans[in[i]];
		if (display) {
			const char *p = ".*Ox#";
			printf("          1      2      3      4      5      6      7      8\n");
			for (int i = 0;i < 100;++i) {
				if (i % 10 == 0) {
					if (i == 0 || i == 90) printf("   ");
					else printf(" %i ", i / 10);
				}
				printf("%-5i ", //aValuationArray[i],
					Values[aValuationArray[i]] + intrans[in[i]]);putchar(p[in[i]]);putchar(' ');
				if (i % 10 == 9) putchar('\n');
			}

		}
		if (use_move_count) {
			int white_moves = 0, black_moves = 0;
			for (int p = 11;p <= 88;++p) if (::move(undo_buffer, p, White, in, Directions, true))white_moves += 3;
			for (int p = 11;p <= 88;++p) if (::move(undo_buffer, p, Black, in, Directions, true))black_moves += 3;

			if (white_moves < 2 && black_moves>2) black_moves <<= 2 - white_moves;
			else if (black_moves < 2 && white_moves>2) white_moves <<= 2 - black_moves;
			sum = sum + white_moves - black_moves;
			/*
			const int corner_fix[] = { 11,22,18,27,81,72,88,77 };

			for (int i = 0;i < 8;i += 2) {
			if (board[corner_fix[i]] == Empty && board[corner_fix[1 + i]] != Empty) {
			if (board[corner_fix[1 + i]] == White) sum -= 700; else sum += 700;
			}
			}

			//11 12 13 14 15 16 17 18
			//21 22 23 24 25 26 27 28
			//31 32 33 34 35 36 37 38
			//41 42 43 44 45 46 47 48
			//51 52 53 54 55 56 57 58
			//61 62 63 64 65 66 67 68
			//71 72 73 74 75 76 77 78
			//81 82 83 84 85 86 87 88

			const int corner_fix3[] = { 11,12,11,21,18,17,18,28,81,71,81,82,88,78,88,87 };

			for (int i = 0;i < 16;i += 2) {
			if (board[corner_fix3[i]] == Empty && board[corner_fix3[1 + i]] != Empty) {
			if (board[corner_fix3[1 + i]] == White) sum -= 450; else sum += 450;
			}
			}


			const int corner_fix2[] = { 11,18,81,88 };
			for (int i = 0;i < 4;++i) {
			if (board[corner_fix[i]] == Empty) {
			if (board[corner_fix[1]] == White) sum += 1600; else sum -= 1600;
			}
			}
			*/
		}

		if (root_color == Black) sum = -sum;
		//? how to count options?

		return sum;
	}

};

Valuator valuator;

int Board::find_move(int depth, Square color, bool use_move_count)
{
	int empty_depth = valuator.find_empty(board);
	int moveAt = 0;
	if (empty_depth < 17) {
		printf("endgame ");
		endgame_alphabeta(moveAt, empty_depth, -INT_MAX, INT_MAX, color, color, false);
	}
	else alphabeta(moveAt, depth, -INT_MAX, INT_MAX, color, color, use_move_count);
	return moveAt;
}

int Board::endgame_alphabeta(int &move_at, int depth, int alpha, int beta, Square color, Square root_color, bool passed)
{
	if (depth == 0) {
		return valuator.find_simple_value(board, root_color);
	}
	int at, move_number = 0;
	int inner_move;
	if (color == root_color) { //maximizing
		int v = -INT_MAX;
		while (next_move(move_number, at, color)) {

			int n = endgame_alphabeta(inner_move, depth - 1, alpha, beta, other_color(color), root_color);
			if (n > v) {
				v = n;
				move_at = at;
				killer(move_number - 1, color);
			}
			if (v > alpha) {
				alpha = v;
			}

			undo(undo_buffer, board);
			if (beta <= alpha) {
				break; //cut off
			}
		}
		if (v == -INT_MAX) {
			if (passed) return valuator.find_simple_value(board, root_color);
			move_at = 0;
			return endgame_alphabeta(inner_move, depth, alpha, beta, other_color(color), root_color, true);//passed
		}
		return v;
	}
	else {//minimizing
		int v = INT_MAX;
		while (next_move(move_number, at, color)) {
			int n = endgame_alphabeta(inner_move, depth - 1, alpha, beta, other_color(color), root_color);
			if (n < v) {
				v = n;
				move_at = at;
				killer(move_number - 1, color);
			}
			if (v < beta) {
				beta = v;
			}
			undo(undo_buffer, board);
			if (beta <= alpha) {
				break; //cut off
			}
		}
		if (v == INT_MAX) {
			if (passed) return valuator.find_simple_value(board, root_color);
			move_at = 0;
			return endgame_alphabeta(inner_move, depth, alpha, beta, other_color(color), root_color, true);//passed
		}
		move_at = at;
		return v;
	}

};

int Board::alphabeta(int &move_at, int depth, int alpha, int beta, Square color, Square root_color, bool use_move_count)
{
	if (depth == 0) {
		return valuator.find_value(board, root_color, use_move_count, false);
	}
	int at, move_number = 0;
	int inner_move;
	if (color == root_color) { //maximizing
		int v = -INT_MAX;
		while (next_move(move_number, at, color)) {

			int n = alphabeta(inner_move, depth - 1, alpha, beta, other_color(color), root_color, use_move_count);
			if (n > v) {
				v = n;
				move_at = at;
				killer(move_number - 1, color);
			}
			if (v > alpha) {
				alpha = v;
			}

			undo(undo_buffer, board);
			if (beta <= alpha) {
				break; //cut off
			}
		}
		if (v == -INT_MAX) {
			move_at = 0;
			return alphabeta(inner_move, depth - 1, alpha, beta, other_color(color), root_color, use_move_count);//passed
		}
		return v;
	}
	else {//minimizing
		int v = INT_MAX;
		while (next_move(move_number, at, color)) {
			int n = alphabeta(inner_move, depth - 1, alpha, beta, other_color(color), root_color, use_move_count);
			if (n < v) {
				v = n;
				move_at = at;
				killer(move_number - 1, color);
			}
			if (v < beta) {
				beta = v;
			}
			undo(undo_buffer, board);
			if (beta <= alpha) {
				break; //cut off
			}
		}
		if (v == INT_MAX) {
			move_at = 0;
			return alphabeta(inner_move, depth - 1, alpha, beta, other_color(color), root_color, use_move_count);//passed
		}
		move_at = at;
		return v;
	}

};

int main()
{
	Board b;
	bool black_passed;
	bool white_passed;
	do {
		if (!b.can_move(Black)) {
			if (white_passed) {
				printf("game over\n");
				break;
			}
			printf("Black must pass \n");
			black_passed = true;
		}
			else {
			b.input(Black,"a:");
			black_passed = false;
		}
//		valuator.find_value(b.board, White,false, true);
		if (!b.can_move(White)) {
			if (black_passed) {
				printf("game over\n");
				break;
			}
			printf("White must pass \n");
			white_passed = true;
		}
		else {
			b.input(White,"a:");
			white_passed = false;
		}
//		valuator.find_value(b.board, Black, false,true);
	} while (true);
	b.print();
	getchar();
    return 0;
}

