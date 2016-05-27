// consolegame.cpp : Defines the entry point for the console application.
//

#include "stdafx.h"
#include <functional>
#include <assert.h>

typedef unsigned Square;
const Square Out = 4;
const Square Empty = 0;
const Square White = 1;
const Square Black = 2;

typedef Square BoardArray[100];
typedef Square BoardLineArray[10];
const int NUMDIR = 8;
const int Directions[] = { 11,9,-11,-9,1,-1,10,-10,0 };
const int LineDirections[] = { 1,-1,0 };

struct ValTriple { int pos; int dir; int len; };
int *safety[8];
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
	{0,0,0}
};
                    /*x,0,x,x,x,x,x,x,x,2,4,6*/
const int shifts[] = {-1,0,-1,-1,-1,-1,-1,-1,-1,2,4,6};
typedef int ValuationArray[100];
ValuationArray aValuationArray;

Square undo_buffer_array[64 * 10];
Square *undo_buffer = &undo_buffer_array[0];

inline Square other_color(Square c) { return (Black + White) ^ c; }

//note white is positive, black negative
//add number of pieces to this
int Values[256];
static int values_by_color[] = { -64,-32,-16,-8,0,8,16,32,64 };
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
				}else ++count_white;
				break;
			case 2:
				if (count_white) {
					--count_white;
					++count_ambig;
				}else ++count_black;
				break;
			case 3:
				++count_ambig;
			}

		}
		Values[i] = values_by_color[count_white - count_black + 4] >> count_ambig;
	}
}

bool move(Square *&undo, int pos, Square color,Square *board, const int *directions, bool check = false)
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


class Board {
public:
	Board() {
		for (int i = 0;i < 100;++i) board[i] = Empty;
		for (int i = 0;i < 9;++i) {
			board[90-i*10]=board[99-i]=board[9+i*10]=board[i] = Out;
		}
		board[44] = board[55] = White;
		board[45] = board[54] = Black;
	}
	bool move(Square *&undo, int pos, Square color) {
		return ::move(undo, pos, color, board, Directions);
	}
	void undo(Square *&undo, Square *board)
	{
		::undo(undo, board);
	}
	BoardArray board;
	void print()
	{
		const char *p = ".*Ox#";
		printf("     1 2 3 4 5 6 7 8\n");
		for (int i = 0;i < 100;++i) {
			if (i % 10 == 0) {
				if (i == 0 || i == 90) printf("   ");
				else printf(" %i ", i / 10);
			}
			putchar(p[board[i]]);putchar(' ');
			if (i % 10 == 9) putchar('\n');
		}
	}

	int alphabeta(int &move_at,int depth, int alpha, int beta, Square color, Square root_color);
	bool next_move(int &move_number,int &move_at,Square color)
	{
		//make killer move lru later
		int at = move_at;
		if (move_number == 0) at = 11;
		else ++at;
		while (!move(undo_buffer, at, color) && at <= 88) ++at;
		if (at <= 88) {
			++move_number;
			move_at = at;
			return true;
		}
		return false;
	}

	int find_move( int depth, Square color )
	{
		int moveAt=0;
		alphabeta(moveAt,depth, -INT_MAX, INT_MAX, color,color);
		return moveAt;
	}

	void input(Square color,const char *command=NULL)
	{
		do {
			char buf[20];
			print();
			if (color == White) fputs("White's", stdout);
			else fputs("Black's", stdout);
			fputs(" move (p for pass, u undo, a[n] auto):", stdout);
			if (command) strcpy(buf, command);
			else fgets(buf, sizeof(buf) - 1, stdin);
			int i = -1;
			sscanf(buf, "%i", &i);
			if (buf[0] == 'p') return;

			if (buf[0] == 'a') {
				int m = find_move(buf[1] - '0', color);
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

	int CalcSafety(int len,int c)//note board is one input, undo_buffer another
	{
		for (int p = 0;p < len;++p) {
			for (int color = White; color <= Black;++color) {
				if (board[p+1] == Empty) {
					if (move(undo_buffer, p+1, color)) {
						for (int s = 0;s < len;++s) c |= board[s+1] << (s + s);
						c |= CalcSafety(len, c);
						undo(undo_buffer);
					}
					else {
						board[p+1] = color;
						c |= color << (p + p);
						c |= CalcSafety(len, c);
						board[p+1] = Empty;
					}
				}
			}
		}
		return c;
	}
	void CalcValuate(int len)
	{
		board[len + 1] = Out;
		for (int c = 0;c < 1<<(len+len);++c) {
			for (int i = 0;i < len;++i) {
				int mask = 3 << (i + i);
				if ((c&mask) == mask) goto cont_c;
				board[i + 1] = (c&mask) >> (i + i);
			}
			//the board line now has every starting position
			//do every possible move from this position, and or the results
			//every square that isn't 3 is safe.
			//calc safety[i-1][c]
			safety[len-1][c] = (((c&0xaaaaaaaa)>>1)|((c & 0x55555555) << 1)|c) & CalcSafety(len,c);
			//printf("safety len=%i[%x]=%x\n",len,c,safety[len - 1][c]);
		cont_c:;
		}
	}

	Valuator() {
		int len = 4;
		for (int i = 1;i <= 8;++i) {
			safety[i - 1] = new int[len];
			memset(safety[i - 1],0,len*sizeof(safety[i - 1][0]));
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
		for (int i = 1;i <= 8;++i) delete [] safety[i - 1];
	}
	bool move(Square *&undo, int pos, Square color, bool check=false) {
		return ::move(undo, pos, color, board, LineDirections);
	}
	void undo(Square *&undo)
	{
		::undo(undo, board);
	}
	//{}{}{} corner not valued properly!!!
	int find_value( BoardArray in,Square root_color, bool display=false)
	{
		for (int i = 11;i <= 88;++i) aValuationArray[i] = 0;
		for (int i = 0;Valuations[i].pos; ++i) {
			int c = 0;
			for (int j = Valuations[i].pos, k = 1;k <= Valuations[i].len;++k, j = j + Valuations[i].dir) {
				c = (c << 2) + in[j];
			
			}
			c = safety[Valuations[i].len - 1][c];
			int s = shifts[Valuations[i].dir];
			assert(s >= 0);
			for (int j = Valuations[i].pos+Valuations[i].dir*(Valuations[i].len-1), k = 1;k <= Valuations[i].len;++k, j = j - Valuations[i].dir) {
				aValuationArray[j] |= (c & 3) << s;
				c >>= 2;
			}
		}
		//at this point I should have a board of safety values to flatten
		int sum = 0;
		static int intrans[] = { 0,1,-1,0,0 };
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
		int white_moves = 0, black_moves = 0;
		for (int p = 11;p <= 88;++p) if (move(undo_buffer, p, White, true))white_moves += 1;
		for (int p = 11;p <= 88;++p) if (move(undo_buffer, p, Black, true))black_moves += 1;

		if (white_moves < 2 && black_moves>2) black_moves <<= 1;
		else if (black_moves < 2 && white_moves>2) white_moves <<= 1;
		sum = sum + white_moves - black_moves;
		if (root_color == Black) sum=-sum;
		//? how to count options?
		
		return sum;
	}
	
};

Valuator valuator;
int Board::alphabeta(int &move_at, int depth, int alpha, int beta, Square color, Square root_color)
{
	if (depth == 0) {
		return valuator.find_value(board, root_color);
	}
	int at, move_number = 0;
	int inner_move;
	if (color == root_color) { //maximizing
		int v = -INT_MAX;
		while (next_move(move_number, at, color)) {

			int n = alphabeta(inner_move,depth-1,alpha, beta, other_color(color), root_color);
			if (n > v) {
				v = n;
				move_at = at;
			}
			if (v > alpha) {
				alpha = v;
			}

			undo(undo_buffer, board);
			if (beta <= alpha)break; //cut off
		}
		if (v == -INT_MAX) {
			move_at = 0;
			return alphabeta(inner_move, depth - 1, alpha, beta, other_color(color), root_color);//passed
		}
		return v;
	}
	else {//minimizing
		int v = INT_MAX;
		while (next_move(move_number, at, color)) {
			int n = alphabeta(inner_move, depth - 1, alpha, beta, other_color(color), root_color);
			if (n < v) {
				v = n;
				move_at = at;
			}
			if (v < beta) {
				beta = v;
			}
			undo(undo_buffer, board);
			if (beta <= alpha)break; //cut off
		}
		if (v == INT_MAX) {
			move_at = 0;
			return alphabeta(inner_move, depth - 1, alpha, beta, other_color(color), root_color);//passed
		}
		move_at = at;
		return v;
	}

}

int main()
{
	Board b;
	do {
		b.input(Black);
		valuator.find_value(b.board, White, true);
		b.input(White);
		valuator.find_value(b.board, Black, true);
	} while (true);

    return 0;
}

