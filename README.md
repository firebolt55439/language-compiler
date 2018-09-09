# "Cobra" Language Compiler
A fully-fledged programming language compiler: fast, performant, and with an LLVM backend, allowing for extensive optimization of code along with assembly code generation. What's not to like?

To get a taste of what the language is capable of and its heavily C-inspired syntax, take a look at the samples (under `sample/`) or any of the test cases (under `tests/`).

Here is a Sudoku solver written in Cobra (the language name is still a work in progress):

```
import stdio;

/**
* I have written my own recursive, backtracking algorithm
* to solve a Sudoku puzzle and this is an implementation
* of my own algorithm in my own programming language.
* Neat, huh?
**/

fn RowContains:bool takes [int[81] grid, int loc, int look]{
	// returns if the row in grid specified by location loc contains number look
	for(let int i = ((loc / 9) * 9); ((i == ((loc / 9) * 9)) || (i % 9)); i = i + 1){
		if(grid[i] == look) return true;
	}
	return false;
}

fn ColContains:bool takes [int[81] grid, int loc, int look]{
	// returns if the col in grid specified by location loc contains number look
	for(let int i = (loc % 9); (i < 81); i = i + 9){
		if(grid[i] == look) return true;
	}
	return false;
}

fn SubgridContains:bool takes [int[81] grid, int loc, int look]{
	// returns if the subgrid in grid specified by location loc contains number look
	let int vi = 0;
	let int vf = 0;
	let int hi = 0;
	let int hf = 0;
	let int c = (loc % 9);
	let int r = (loc / 9);
	if(c < 6){
		if(c < 3){
			vi = 0;
			vf = 2;
		} else {
			vi = 3;
			vf = 5;
		}
	} else {
		vi = 6;
		vf = 8;
	}
	if(r < 6){
		if(r < 3){
			hi = 0;
			hf = 2;
		} else {
			hi = 3;
			hf = 5;
		}
	} else {
		hi = 6;
		hf = 8;
	}
	for(let int i = hi; i <= hf; i = i + 1){
		for(let int j = vi; j <= vf; j = j + 1){
			if(grid[(9 * i) + j] == look) return true;
		}
	}
	return false;
}

fn SolveLocation:bool[9] takes [int[81] grid, int loc]{
	// returns a heap-allocated boolean array from [0] --> [8] detailing which 
	// numbers can and cannot go on the spot
	let bool* ret = malloc(9);
	for(let int i = 0; i < 9; i = i + 1){
		ret[i] = false;
	}
	for(let int n = 1; n <= 9; n = n + 1){
		if((!RowContains(grid, loc, n)) && (!ColContains(grid, loc, n)) && (!SubgridContains(grid, loc, n))){
			//printf("%d works.\n", n);
			ret[n - 1] = true;
		}
	}
	return ret;
}

fn SolveSudoku:bool takes [int[81] grid, int loc]{
	//printf("Called for loc. [%d][%d]\n", (loc / 9), (loc % 9));
	let int ind = loc;
	if(ind >= 81) return true; // done with puzzle
	if(grid[ind]){ // if already solved for
		return cast(SolveSudoku(grid, (loc + 1)), bool);
	}
	let bool* possibs = SolveLocation(grid, loc);
	let bool had_one = false;
	for(let int i = 0; i < 9; i = i + 1){
		if(possibs[i]){
			had_one = true;
			//printf("Possiblity of %d.\n", (i + 1));
		}
	}
	if(had_one == false) return false; // failed - no possible solutions
	loc = loc + 1; // set loc to next location
	for(let int i = 0; i < 9; i = i + 1){
		if(possibs[i]){
			had_one = true;
			//printf("Trying possiblity of %d...\n", (i + 1));
			grid[ind] = (i + 1);
			let bool r = SolveSudoku(grid, loc); // loc = next location now
			if(r){
				//printf("Worked! Unwinding...\n");
				free(possibs);
				return true;
			}
			grid[ind] = 0; // backtrack - only done for dumping purposes, could *technically* be removed
		}
	}
	free(possibs);
	return false;
}

fn main:i32 takes [int argc, char** argv]{
	// You can change the 9x9 grid below — it is the input to the solving
	// function. Copy down anything you would like to solve :)
	dec array:int grid = {
		5, 3, 0, 0, 7, 0, 0, 0, 0,
		6, 0, 0, 1, 9, 5, 0, 0, 0, 
		0, 9, 8, 0, 0, 0, 0, 6, 0, 
		8, 0, 0, 0, 6, 0, 0, 0, 3,
		4, 0, 0, 8, 0, 3, 0, 0, 1,
		7, 0, 0, 0, 2, 0, 0, 0, 6,
		0, 6, 0, 0, 0, 0, 2, 8, 0, 
		0, 0, 0, 4, 1, 9, 0, 0, 5,
		0, 0, 0, 0, 8, 0, 0, 7, 9
	}; // 0 = don't know yet
	if(SolveSudoku(grid, 0)){
		printf("Success!\n");
	} else printf("Failure.\n");
	printf("---------------------------\n");
	for(let int i = 0; i < 9; i = i + 1){
		for(let int j = 0; j < 9; j = j + 1){
			printf("%d ", grid[(9 * i) + j]);
			if((((j - 2) % 3) == 0) && (j < 8)) printf("|");
			printf(" ");
		}
		printf("\n");
		if(((i - 2) % 3) == 0) printf("---------------------------");
		printf("\n");
	}
	return 0;
}
```

## Contribution
Feel free to contribute — just hit me up with a pull request.

## Why so monolithic?
Apologies for the extreme monolithical design. I wrote this language about ~3 years ago, before I understood some of the tenets of modular code.































































