
#include <cmath>
#include <cassert>
#include "basis_pms.h"
#include <sstream>
#include <algorithm>
#include <chrono>
using namespace std;
typedef long long ll;
int num_vars, num_clauses, ori_var_num, ori_clause_num;
ll top_clause_weight;
int *clause_lit_count; // amount of literals in each clause
ll *org_clause_weight;
int *clause_true_lit_thres;
int *fix_var;
int la_idx = -1, la_val = 0;
vector<vector<lit>> watch;
lit **ori_clause_lit;
ll *ori_org_clause_weight;
int *ori_clause_lit_count; 
int *ori_clause_true_lit_thres;

Satlike::Satlike()
{
	/**********PRS added************/
	best_flips = 0;
	cccheck = 1;

	problem_weighted = 1;
	partial = 1; // 1 if the instance has hard clauses, and 0 otherwise.

	max_clause_length = 0;
	min_clause_length = 100000000;

	// size of the instance
	num_vars = 0;	 // var index from 1 to num_vars
	num_clauses = 0; // clause index from 0 to num_clauses-1
	num_hclauses = 0;
	num_sclauses = 0;

	print_time = 240;
	cutoff_time = 300;
}

void Satlike::settings()
{
	// steps
	max_tries = 100000000;
	max_flips = 200000000;
	max_non_improve_flip = 10000000;

	large_clause_count_threshold = 0;
	soft_large_clause_count_threshold = 0;

	rdprob = 0.01;
	hd_count_threshold = 15;
	rwprob = 0.1;
	smooth_probability = 0.01;

	h_inc = 1;
	coeff = 1.0;
	coeff_inc = 1.1;
	coeff_dec = 1.1;

	if (num_vars > 2000)
	{
		rdprob = 0.01;
		hd_count_threshold = 15;
		rwprob = 0.1;
		smooth_probability = 0.0000001;
	}
}

void Satlike::allocate_memory()
{
	int malloc_var_length = num_vars + 10;
	int malloc_clause_length = num_clauses + 10;

	unit_clause = new lit[malloc_clause_length];

	var_lit = new lit *[malloc_var_length];
	var_lit_count = new int[malloc_var_length];
	// clause_lit = new lit *[malloc_clause_length];
	// clause_lit_count = new int[malloc_clause_length];
	// clause_true_lit_thres = new int[malloc_clause_length];

	score = new long long[malloc_var_length];
	sscore = new long long[malloc_var_length];
	oscore = new long long[malloc_var_length];
	var_neighbor = new int *[malloc_var_length];
	var_neighbor_count = new int[malloc_var_length];
	time_stamp = new long long[malloc_var_length];
	neighbor_flag = new int[malloc_var_length];
	temp_neighbor = new int[malloc_var_length];

	// org_clause_weight = new long long[malloc_clause_length];
	clause_weight = new long long[malloc_clause_length];
	unit_weight = new long long[malloc_clause_length];
	org_unit_weight = new long long[malloc_clause_length];
	sat_count = new int[malloc_clause_length];

	hardunsat_stack = new int[malloc_clause_length];
	index_in_hardunsat_stack = new int[malloc_clause_length];
	softunsat_stack = new int[malloc_clause_length];
	index_in_softunsat_stack = new int[malloc_clause_length];

	unsatvar_stack = new int[malloc_var_length];

	goodvar_stack = new int[malloc_var_length];
	already_in_goodvar_stack = new int[malloc_var_length];

	cur_soln = new int[malloc_var_length];
	best_soln = new int[malloc_var_length];

	large_weight_clauses = new int[malloc_clause_length];

	temp_lit = new int[malloc_var_length];
}

void Satlike::free_memory()
{
	int i;
	// for (i = 0; i < num_clauses; i++)
	// 	delete[] clause_lit[i];

	delete[] var_lit;
	delete[] var_lit_count;
	delete[] clause_lit;
	delete[] clause_lit_count;
	delete[] clause_true_lit_thres;

	delete[] score;
	delete[] oscore;
	delete[] sscore;
	delete[] var_neighbor;
	delete[] var_neighbor_count;
	delete[] time_stamp;
	delete[] neighbor_flag;
	delete[] temp_neighbor;

	delete[] org_clause_weight;
	delete[] clause_weight;
	delete[] unit_weight;
	delete[] org_unit_weight;
	delete[] sat_count;

	delete[] hardunsat_stack;
	delete[] index_in_hardunsat_stack;
	delete[] softunsat_stack;
	delete[] index_in_softunsat_stack;

	delete[] unsatvar_stack;

	delete[] goodvar_stack;
	delete[] already_in_goodvar_stack;

	delete[] cur_soln;
	delete[] best_soln;

	delete[] large_weight_clauses;

	delete[] temp_lit;

	delete[] unit_clause;
}

void Satlike::build_neighbor_relation()
{
	int i, j, count;
	int v, c, n;
	int temp_neighbor_count;

	for (v = 1; v <= num_vars; ++v)
	{
		neighbor_flag[v] = 1;
		temp_neighbor_count = 0;

		for (i = 0; i < var_lit_count[v]; ++i)
		{
			c = var_lit[v][i].clause_num;
			for (j = 0; j < clause_lit_count[c]; ++j)
			{
				n = clause_lit[c][j].var_num;
				if (neighbor_flag[n] != 1)
				{
					neighbor_flag[n] = 1;
					temp_neighbor[temp_neighbor_count++] = n;
				}
			}
		}

		neighbor_flag[v] = 0;

		var_neighbor[v] = new int[temp_neighbor_count];
		var_neighbor_count[v] = temp_neighbor_count;

		count = 0;
		for (i = 0; i < temp_neighbor_count; i++)
		{
			var_neighbor[v][count++] = temp_neighbor[i];
			neighbor_flag[temp_neighbor[i]] = 0;
		}
	}
}

void Satlike::build_instance()
{
	allocate_memory();
	for (int v = 1; v <= num_vars; ++v)
	{
		var_lit_count[v] = 0;
		var_lit[v] = NULL;
	}
	int i, v, c;
	num_hclauses = num_sclauses = 0;
	unit_clause_count = 0;
	total_soft_weight = 0;
	c = 0;
	first_soft_clause_id = num_clauses;
	while (c < num_clauses)
	{
		// printf("top_clause_weight:	%d,%d\n", org_clause_weight[c], top_clause_weight);
		if (org_clause_weight[c] != top_clause_weight)
		{
			total_soft_weight += org_clause_weight[c];
			num_sclauses++;
			if (first_soft_clause_id == num_clauses)
				first_soft_clause_id = c;
		}
		else
			num_hclauses++;

		for (i = 0; i < clause_lit_count[c]; ++i) {
			// printf("%d %d %d", i, clause_lit_count[c], clause_lit[c][i].var_num);
			var_lit_count[clause_lit[c][i].var_num]++;
		}

		if (clause_lit_count[c] == 1)
			unit_clause[unit_clause_count++] = clause_lit[c][0];
		if (clause_lit_count[c] > max_clause_length)
			max_clause_length = clause_lit_count[c];
		if (clause_lit_count[c] < min_clause_length)
			min_clause_length = clause_lit_count[c];
		c++;
	}
	// printf("first_soft_clause_id:	%d\n", first_soft_clause_id);
	// creat var literal arrays
	for (v = 1; v <= num_vars; ++v)
	{
		var_lit[v] = new lit[var_lit_count[v] + 1];
		var_lit_count[v] = 0; // reset to 0, for build up the array
	}
	// scan all clauses to build up var literal arrays
	for (c = 0; c < num_clauses; ++c)
	{
		for (i = 0; i < clause_lit_count[c]; ++i)
		{
			// printf("%d,%d\n",clause_lit[c][i].var_num,var_lit_count[v]);
			v = clause_lit[c][i].var_num;
			var_lit[v][var_lit_count[v]] = clause_lit[c][i];
			++var_lit_count[v];
		}
	}
	for (v = 1; v <= num_vars; ++v)
		var_lit[v][var_lit_count[v]].clause_num = -1;
	build_neighbor_relation();
	best_soln_feasible = 0;
	opt_unsat_weight = total_soft_weight + 1;
}


void Satlike::init(vector<int> &init_solution)
{
	int v, c;
	int j;


	local_soln_feasible = 0;
	local_opt_unsat_weight = top_clause_weight + 1;
	large_weight_clauses_count = 0;

	if (num_sclauses > 0)
		ave_soft_weight = total_soft_weight / num_sclauses;
	ave_hard_weight = 0;
	inc_hard_weight = 0;
	// cout << "ave soft weight is " << ave_soft_weight << endl;
	// Initialize clause information
	for (c = 0; c < num_clauses; c++)
	{

		if (org_clause_weight[c] == top_clause_weight)
		{
			// clause_weight[c] = clause_true_lit_thres[c];
			org_unit_weight[c] = 1;
			unit_weight[c] = org_unit_weight[c];
			long long total_sum = 0;
			for (int i = 0; i < clause_lit_count[c]; ++i)
			{
				total_sum += clause_lit[c][i].weight;
			}
			clause_weight[c] = total_sum / clause_lit_count[c];
			ave_hard_weight += clause_weight[c];
		}
		else
		{
			clause_weight[c] = org_clause_weight[c];
			org_unit_weight[c] = ceil((double)clause_weight[c] / (double)clause_true_lit_thres[c]);
			unit_weight[c] = org_unit_weight[c];
		}
	}
	if (num_hclauses > 0)
	{
		inc_hard_weight = ave_hard_weight % num_hclauses;
		ave_hard_weight /= num_hclauses;
		inc_hard_weight += ave_soft_weight;
	}

	// cout << "inc hard weight is " << inc_hard_weight << endl;
	// cout << "ave hard weight is " << ave_hard_weight << endl;

	// init solution
	if (init_solution.size() == 0)
	{
		for (v = 1; v <= num_vars; v++)
		{
			cur_soln[v] = 0;
			time_stamp[v] = 0;
		}
	}
	else
	{
		for (v = 1; v <= num_vars; v++)
		{
			cur_soln[v] = init_solution[v];
			if (cur_soln[v] == 2)
				cur_soln[v] = rand() % 2;
			time_stamp[v] = 0;
		}
	}

	// init stacks
	hard_unsat_nb = 0;
	hardunsat_stack_fill_pointer = 0;
	softunsat_stack_fill_pointer = 0;
	unsatvar_stack_fill_pointer = 0;
	/* figure out sat_count, sat_var, soft_unsat_weight and init unsat_stack */
	soft_unsat_weight = 0;

	for (c = 0; c < num_clauses; ++c)
	{
		sat_count[c] = 0;
		for (j = 0; j < clause_lit_count[c]; ++j)
		{

			if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
			{
				sat_count[c] += clause_lit[c][j].weight;
			}
		}
		if (sat_count[c] < clause_true_lit_thres[c])
		{
			if (org_clause_weight[c] != top_clause_weight)
				soft_unsat_weight += (clause_true_lit_thres[c] - sat_count[c]) * org_unit_weight[c];
			unsat(c);
		}
	}

	/*figure out score*/
	int sense, weight;
	for (v = 1; v <= num_vars; v++)
	{
		score[v] = 0;
		sscore[v] = 0;
		for (int i = 0; i < var_lit_count[v]; ++i)
		{
			c = var_lit[v][i].clause_num;
			sense = var_lit[v][i].sense;
			weight = var_lit[v][i].weight;
			if (org_clause_weight[c] == top_clause_weight)
			{
				if (sat_count[c] < clause_true_lit_thres[c])
				{
					if (sense != cur_soln[v])
					{
						score[v] += unit_weight[c] * min(clause_true_lit_thres[c] - sat_count[c], weight);
					}
					else
						score[v] -= unit_weight[c] * weight;
				}
				else if (sat_count[c] >= clause_true_lit_thres[c])
				{
					if (sense == cur_soln[v])
					{
						score[v] -= unit_weight[c] * max(0, clause_true_lit_thres[c] - sat_count[c] + weight);
					}
				}
			}
			else
			{
				if (sat_count[c] < clause_true_lit_thres[c])
				{
					if (sense != cur_soln[v])
					{
						sscore[v] += unit_weight[c] * min(clause_true_lit_thres[c] - sat_count[c], weight);
					}
					else
						sscore[v] -= unit_weight[c] * weight;
				}
				else if (sat_count[c] >= clause_true_lit_thres[c])
				{
					if (sense == cur_soln[v])
					{
						sscore[v] -= unit_weight[c] * max(0, clause_true_lit_thres[c] - sat_count[c] + weight);
					}
				}
			}
		}
	}

	// init goodvars stack
	goodvar_stack_fill_pointer = 0;
	for (v = 1; v <= num_vars; v++)
	{
		if (score[v] + coeff * sscore[v] > 0)
		{
			already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
			mypush(v, goodvar_stack);
		}
		else
			already_in_goodvar_stack[v] = -1;
	}
}

int Satlike::pick_var()
{
	int i, v;
	int best_var;

	if (goodvar_stack_fill_pointer > 0)
	{
		if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rdprob)
			return goodvar_stack[rand() % goodvar_stack_fill_pointer];

		if (goodvar_stack_fill_pointer < hd_count_threshold)
		{
			best_var = goodvar_stack[0];
			for (i = 1; i < goodvar_stack_fill_pointer; ++i)
			{
				v = goodvar_stack[i];
				if (score[v] + coeff * sscore[v] > score[best_var] + coeff * sscore[best_var])
					best_var = v;
				else if (score[v] + coeff * sscore[v] == score[best_var] + coeff * sscore[best_var])
				{
					if (time_stamp[v] < time_stamp[best_var])
						best_var = v;
				}
			}
			return best_var;
		}
		else
		{

			int r = rand() % goodvar_stack_fill_pointer;
			best_var = goodvar_stack[r];

			for (i = 1; i < hd_count_threshold; ++i)
			{
				r = rand() % goodvar_stack_fill_pointer;
				v = goodvar_stack[r];
				if (score[v] + coeff * sscore[v] > score[best_var] + coeff * sscore[best_var])
					best_var = v;
				else if (score[v] + coeff * sscore[v] == score[best_var] + coeff * sscore[best_var])
				{
					if (time_stamp[v] < time_stamp[best_var])
						best_var = v;
				}
			}
			return best_var;
		}
	}
	update_clause_weights();
	int sel_c;
	lit *p;

	if (hardunsat_stack_fill_pointer > 0)
	{
		sel_c = hardunsat_stack[rand() % hardunsat_stack_fill_pointer];
	}
	else
	{
		sel_c = softunsat_stack[rand() % softunsat_stack_fill_pointer];
	}
	if ((rand() % MY_RAND_MAX_INT) * BASIC_SCALE < rwprob)
		return clause_lit[sel_c][rand() % clause_lit_count[sel_c]].var_num;
	best_var = clause_lit[sel_c][0].var_num;
	p = clause_lit[sel_c];
	for (p++; (v = p->var_num) != 0; p++)
	{
		if (score[v] + coeff * sscore[v] > score[best_var] + coeff * sscore[best_var])
			best_var = v;
		else if (score[v] + coeff * sscore[v] == score[best_var] + coeff * sscore[best_var])
		{
			if (time_stamp[v] < time_stamp[best_var])
				best_var = v;
		}
	}
	return best_var;
}

void Satlike::update_goodvarstack1(int flipvar)
{
	int v;

	// remove the vars no longer goodvar in goodvar stack
	for (int index = goodvar_stack_fill_pointer - 1; index >= 0; index--)
	{
		v = goodvar_stack[index];
		if (score[v] + coeff * sscore[v] <= 0)
		{
			int top_v = mypop(goodvar_stack);
			goodvar_stack[index] = top_v;
			already_in_goodvar_stack[top_v] = index;
			already_in_goodvar_stack[v] = -1;
		}
	}

	// if (cccheck == 0 && score[flipvar] + coeff * sscore[flipvar] > 0 && already_in_goodvar_stack[flipvar] == -1)
	// {
	// 	already_in_goodvar_stack[flipvar] = goodvar_stack_fill_pointer;
	// 	mypush(flipvar, goodvar_stack);
	// }
	for (int i = 0; i < var_neighbor_count[flipvar]; ++i)
	{
		v = var_neighbor[flipvar][i];
		if (score[v] + coeff * sscore[v] > 0)
		{
			if (already_in_goodvar_stack[v] == -1)
			{
				already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
				mypush(v, goodvar_stack);
			}
		}
	}
}

void Satlike::flip(int flipvar)
{
// printf("%.2lf\n", coeff);
	int i, v, c;
	int index;
	lit *clause_c;
	int weight;
	int gap;

	int org_flipvar_score = score[flipvar];
	int org_sscore = sscore[flipvar];
	cur_soln[flipvar] = 1 - cur_soln[flipvar];

	for (i = 0; i < var_lit_count[flipvar]; ++i)
	{
		c = var_lit[flipvar][i].clause_num;
		clause_c = clause_lit[c];
		weight = var_lit[flipvar][i].weight;
		if (org_clause_weight[c] == top_clause_weight)
		{
			if (cur_soln[flipvar] == var_lit[flipvar][i].sense)
			{
				if (org_clause_weight[c] != top_clause_weight && sat_count[c] < clause_true_lit_thres[c])
				{
					soft_unsat_weight -= org_unit_weight[c] * min(weight, clause_true_lit_thres[c] - sat_count[c]);
				}
				// sat_count[c] += weight;

				if (sat_count[c] + weight <= clause_true_lit_thres[c])
				{
					gap = clause_true_lit_thres[c] - sat_count[c];
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						if (p->sense != cur_soln[v])
						{
							score[v] -= (unit_weight[c] * (min(gap, p->weight) - min(gap - weight, p->weight)));
							
						}
					}
				}
				else if (sat_count[c] <= clause_true_lit_thres[c]) // sat_count[c]+weight > clause_true_lit_thres[c]
				{
					gap = clause_true_lit_thres[c] - sat_count[c];
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						if (p->sense != cur_soln[v])
						{
							score[v] -= (unit_weight[c] * min(gap, p->weight));
							
						}
						else
						{
							score[v] += unit_weight[c] * (p->weight - max(0, gap - weight + p->weight));
						}
					}
				}
				else // sat_count[c]+weight > clause_true_lit_thres[c], sat_count[c] > clause_true_lit_thres[c]
				{
					gap = clause_true_lit_thres[c] - sat_count[c];
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						if (p->sense == cur_soln[v])
						{
							score[v] += unit_weight[c] * (max(0, gap + p->weight) - max(0, gap - weight + p->weight));
							
						}
					}
				}
				if (sat_count[c] < clause_true_lit_thres[c] && sat_count[c] + weight >= clause_true_lit_thres[c])
				{
					sat(c);
				}
				sat_count[c] += weight;
			}
			else // cur_soln[flipvar] != cur_lit.sense
			{
				//--sat_count[c];
				if (org_clause_weight[c] != top_clause_weight && sat_count[c] - weight < clause_true_lit_thres[c])
				{
					soft_unsat_weight += org_unit_weight[c] * min(weight, clause_true_lit_thres[c] - sat_count[c] + weight);
				}

				if (sat_count[c] - weight >= clause_true_lit_thres[c])
				{
					gap = clause_true_lit_thres[c] - sat_count[c];
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						if (p->sense == cur_soln[v])
						{
							score[v] -= unit_weight[c] * (max(0, gap + weight + p->weight) - max(0, gap + p->weight));
							
						}
					}
				}
				else if (sat_count[c] >= clause_true_lit_thres[c])
				{
					gap = clause_true_lit_thres[c] - sat_count[c];
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						if (p->sense == cur_soln[v])
						{
							score[v] -= unit_weight[c] * (p->weight - max(0, gap + p->weight));
							
						}
						else
						{
							score[v] += unit_weight[c] * min(p->weight, gap + weight);
							
						}
					}
				}
				else
				{
					gap = clause_true_lit_thres[c] - sat_count[c];
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						if (p->sense != cur_soln[v])
						{
							score[v] += unit_weight[c] * (min(p->weight, gap + weight) - min(p->weight, gap));
						}
					}
				}
				if (sat_count[c] >= clause_true_lit_thres[c] && sat_count[c] - weight < clause_true_lit_thres[c])
				{
					unsat(c);
				}
				sat_count[c] -= weight;

			} // end else
		}
		else
		{
			if (cur_soln[flipvar] == var_lit[flipvar][i].sense)
			{
				if (org_clause_weight[c] != top_clause_weight && sat_count[c] < clause_true_lit_thres[c])
				{
					soft_unsat_weight -= org_unit_weight[c] * min(weight, clause_true_lit_thres[c] - sat_count[c]);
				}
				// sat_count[c] += weight;

				if (sat_count[c] + weight <= clause_true_lit_thres[c])
				{
					gap = clause_true_lit_thres[c] - sat_count[c];
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						if (p->sense != cur_soln[v])
						{
							sscore[v] -= (unit_weight[c] * (min(gap, p->weight) - min(gap - weight, p->weight)));
							
						}
					}
				}
				else if (sat_count[c] <= clause_true_lit_thres[c]) // sat_count[c]+weight > clause_true_lit_thres[c]
				{
					gap = clause_true_lit_thres[c] - sat_count[c];
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						if (p->sense != cur_soln[v])
						{
							sscore[v] -= (unit_weight[c] * min(gap, p->weight));
							
						}
						else
						{
							sscore[v] += unit_weight[c] * (p->weight - max(0, gap - weight + p->weight));
							
						}
					}
				}
				else // sat_count[c]+weight > clause_true_lit_thres[c], sat_count[c] > clause_true_lit_thres[c]
				{
					gap = clause_true_lit_thres[c] - sat_count[c];
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						if (p->sense == cur_soln[v])
						{
							sscore[v] += unit_weight[c] * (max(0, gap + p->weight) - max(0, gap - weight + p->weight));
							
						}
					}
				}
				if (sat_count[c] < clause_true_lit_thres[c] && sat_count[c] + weight >= clause_true_lit_thres[c])
				{
					sat(c);
				}
				sat_count[c] += weight;
			}
			else // cur_soln[flipvar] != cur_lit.sense
			{
				//--sat_count[c];
				if (org_clause_weight[c] != top_clause_weight && sat_count[c] - weight < clause_true_lit_thres[c])
				{
					soft_unsat_weight += org_unit_weight[c] * min(weight, clause_true_lit_thres[c] - sat_count[c] + weight);
				}

				if (sat_count[c] - weight >= clause_true_lit_thres[c])
				{
					gap = clause_true_lit_thres[c] - sat_count[c];
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						if (p->sense == cur_soln[v])
						{
							sscore[v] -= unit_weight[c] * (max(0, gap + weight + p->weight) - max(0, gap + p->weight));
							
						}
					}
				}
				else if (sat_count[c] >= clause_true_lit_thres[c])
				{
					gap = clause_true_lit_thres[c] - sat_count[c];
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						if (p->sense == cur_soln[v])
						{
							sscore[v] -= unit_weight[c] * (p->weight - max(0, gap + p->weight));
							
						}
						else
						{
							sscore[v] += unit_weight[c] * min(p->weight, gap + weight);
							
						}
					}
				}
				else
				{
					gap = clause_true_lit_thres[c] - sat_count[c];
					for (lit *p = clause_c; (v = p->var_num) != 0; p++)
					{
						if (p->sense != cur_soln[v])
						{
							sscore[v] += unit_weight[c] * (min(p->weight, gap + weight) - min(p->weight, gap));
							
						}
					}
				}
				if (sat_count[c] >= clause_true_lit_thres[c] && sat_count[c] - weight < clause_true_lit_thres[c])
				{
					unsat(c);
				}
				sat_count[c] -= weight;

			} // end else
		}
	}

	// update information of flipvar
	score[flipvar] = -org_flipvar_score;
	sscore[flipvar] = -org_sscore;
	update_goodvarstack1(flipvar);
}

void Satlike::print_best_solution()
{
	if (best_soln_feasible == 1)
	{
		// printf("%d,%d\n", opt_unsat_weight, wecnf_obj_pre);
		// printf("%d,%d\n", opt_real_weight, real_obj_pre);
		if (verify_sol())
			cout << "B\t" << opt_unsat_weight + wecnf_obj_pre << '\t' << opt_real_weight + real_obj_pre
				 << '\t' << opt_time << '\t' << tries << '\t' << endl;
		else
			cout << "verify solion wrong " << endl;
	}
	else
		cout << "U\t no feasible solution" << endl;
	flush(cout);
	// ofstream ofile("solution.res");
	// ofile << num_vars << " ";
	// for (int i = 1; i <= num_vars; i++)
	// {
	// 	cout << best_soln[i] << " ";
	// }
	// cout << endl;
}

long long Satlike::cal_opb_weight()
{
	long long res = 0;
	for (int i = first_soft_clause_id; i < num_clauses; i++)
	{
		assert(clause_lit_count[i] == 1);
		assert(clause_true_lit_thres[i] == 1);
		assert(clause_lit[i][0].weight == 1);
		if (cur_soln[clause_lit[i][0].var_num])
		{
			// printf("%d(%d) ", clause_lit[i][0].var_num, cur_soln[clause_lit[i][0].var_num]);
			res += org_clause_weight[i] * (clause_lit[i][0].sense == 1 ? -1 : 1);
		}
	}
	// printf("c	%d,%d,%d\n", res, cur_soln[1], first_soft_clause_id);
	// puts("");
	return res;
}

void Satlike::adjust_good_var() {
	for (int v = 1; v <= num_vars; v++)
	{
		int index = already_in_goodvar_stack[v];
		if (score[v] + coeff * sscore[v] <= 0 && index != -1)
		{
			printf("wrong1 %d\n", v);
			int top_v = mypop(goodvar_stack);
			goodvar_stack[index] = top_v;
			already_in_goodvar_stack[top_v] = index;
			already_in_goodvar_stack[v] = -1;
		}
		else if (score[v] + coeff * sscore[v] > 0 && index == -1) {
			already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
			mypush(v, goodvar_stack);
		}
	}
	
}

int Satlike::local_search_with_decimation(vector<int> &init_solution, int should_break)
{
	// printf("local_search_with_decimation...\n");
	settings();
	for (tries = 1; tries < max_tries; ++tries)
	{
		init(init_solution);
		if (should_break) max_flips = 50000000;
		for (step = 1; step < max_flips; ++step)
		{
			if (hard_unsat_nb == 0) feasibles = 1; // can if (hard == 0 && last_find_feasible_step<= step - K)
			if (hard_unsat_nb == 0 && (soft_unsat_weight < opt_unsat_weight || best_soln_feasible == 0))
			{
				// cout << "unsat soft stack fill pointer" << softunsat_stack_fill_pointer << endl;
				if (soft_unsat_weight < top_clause_weight)
				{
					// 记录一下当前step
					best_soln_feasible = 1;
					opt_unsat_weight = soft_unsat_weight;
					for (int v = 1; v <= num_vars; ++v)
						best_soln[v] = cur_soln[v];
					best_flips = step;

					opt_time = get_runtime();
					long long real_weight = cal_opb_weight();
					opt_real_weight = real_weight;
					simple_print();
					// printf("%lld %lld\n", opt_unsat_weight, real_weight);
					if (opt_unsat_weight == 0) return 1;
				}
			}
			if (step % adjust_rounds == 0) {
				if (feasibles) coeff *= coeff_inc;
				else coeff /= coeff_dec;
				coeff = max(coeff, 0.1);
				coeff = min(coeff, 50.0);
				feasibles = 0;
				// adjust_good_var();
			}
			double elapse_time = get_runtime();
			if (elapse_time >= cutoff_time) return -1;
			int flipvar = pick_var();
			flip(flipvar);
			// check_new_score();
			time_stamp[flipvar] = step;
		}
		if (should_break) return 0;
	}
	return 0;
}

void Satlike::check_softunsat_weight()
{
	int c, j, flag;
	long long verify_unsat_weight = 0;

	for (c = 0; c < num_clauses; ++c)
	{
		flag = 0;
		int tem_clause_true_lit_count = 0;
		for (j = 0; j < clause_lit_count[c]; ++j)
		{
			if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
			{
				tem_clause_true_lit_count++;
			}
		}
		if (tem_clause_true_lit_count >= clause_true_lit_thres[c])
			flag = 1;

		if (flag == 0)
		{
			if (org_clause_weight[c] == top_clause_weight) // verify hard clauses
			{
				continue;
			}
			else
			{
				verify_unsat_weight += org_unit_weight[c] * (clause_true_lit_thres[c] - tem_clause_true_lit_count);
			}
		}
	}

	if (verify_unsat_weight != soft_unsat_weight)
	{
		cout << step << endl;
		cout << "verify unsat weight is" << verify_unsat_weight << " and soft unsat weight is " << soft_unsat_weight << endl;
	}
	// return 0;
}

bool Satlike::verify_sol()
{
	int c, j, flag;
	long long verify_unsat_weight = 0;

	for (c = 0; c < num_clauses; ++c)
	{
		flag = 0;
		int tem_clause_true_lit_count = 0;
		for (j = 0; j < clause_lit_count[c]; ++j)
		{
			if (best_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
			{
				tem_clause_true_lit_count += clause_lit[c][j].weight;
			}
		}
		if (tem_clause_true_lit_count >= clause_true_lit_thres[c])
			flag = 1;

		if (flag == 0)
		{
			if (org_clause_weight[c] == top_clause_weight) // verify hard clauses
			{
				// output the clause unsatisfied by the solution
				cout << "c Error: hard clause " << c << " is not satisfied" << endl;

				cout << "c ";
				for (j = 0; j < clause_lit_count[c]; ++j)
				{
					if (clause_lit[c][j].sense == 0)
						cout << "-";
					cout << clause_lit[c][j].var_num << " ";
				}
				cout << endl;
				cout << "c ";
				for (j = 0; j < clause_lit_count[c]; ++j)
					cout << best_soln[clause_lit[c][j].var_num] << " ";
				cout << endl;
				return 0;
			}
			else
			{
				verify_unsat_weight += org_unit_weight[c] * (clause_true_lit_thres[c] - tem_clause_true_lit_count);
				/*
				cout << "c wanning: soft clause " << c << " is not satisfied" << endl;

				cout << "c org clause weight " << org_clause_weight[c] << " " << endl;

				for (j = 0; j < clause_lit_count[c]; ++j)
				{
					if (clause_lit[c][j].sense == 0)
						cout << "-";
					cout << clause_lit[c][j].var_num << " ";
				}
				cout << endl;
				//cout << "c ";
				for (j = 0; j < clause_lit_count[c]; ++j)
					cout << best_soln[clause_lit[c][j].var_num] << " ";
				cout << endl;*/
				// return 0;
			}
		}
	}

	if (verify_unsat_weight == opt_unsat_weight)
		return 1;
	else
	{
		cout << "c Error: find opt=" << opt_unsat_weight << ", but verified opt=" << verify_unsat_weight << endl;
	}
	return 0;
}

void Satlike::simple_print()
{
	if (best_soln_feasible == 1)
	{
		if (verify_sol() == 1)
			cout << opt_unsat_weight << '\t' << opt_real_weight << '\t' << opt_time << '\t' << tries << '\t' << best_flips << endl;
		else
			cout << "solution is wrong " << endl;
	}
	else
		cout << -1 << '\t' << -1 << endl;
	flush(cout);
}

void Satlike::increase_weights()
{
	int i, c, v;
	int weight;

	int flag = 0;
	// long long inc_hard_weight;
	for (i = 0; i < hardunsat_stack_fill_pointer; ++i)
	{
		c = hardunsat_stack[i];

		inc_hard_weight += clause_weight[c];
		// clause_weight[c] += (h_inc * clause_true_lit_thres[c]);
		// cout << "c: " << c << endl;
		unit_weight[c] += h_inc;

		for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
		{
			weight = p->weight;
			if (p->sense != cur_soln[v])
			{
				score[v] += h_inc * min(clause_true_lit_thres[c] - sat_count[c], weight);
				if (score[v] + coeff * sscore[v] > 0 && already_in_goodvar_stack[v] == -1)
				{
					already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
					mypush(v, goodvar_stack);
				}
			}
			else
			{
				score[v] -= h_inc * weight;
				if (already_in_goodvar_stack[v] != -1 && score[v] + coeff * sscore[v] <= 0)
				{
					int top_v = mypop(goodvar_stack);
					goodvar_stack[already_in_goodvar_stack[v]] = top_v;
					already_in_goodvar_stack[top_v] = already_in_goodvar_stack[v];
					already_in_goodvar_stack[v] = -1;
				}
			}
		}
	}

	// cout << "now ave hard weight is " << ave_hard_weight << endl; && ave_soft_weight - ave_hard_weight > 400
	if (soft_unsat_weight >= opt_unsat_weight && (!weighting || ave_soft_weight - ave_hard_weight < 100))
	{
		// flag = 1;
		if (num_sclauses > 0)
		{
			ave_soft_weight += total_soft_weight / num_sclauses;
			inc_hard_weight += total_soft_weight / num_sclauses;
		}
		for (c = 0; c < num_clauses; ++c)
		{
			if (org_clause_weight[c] == top_clause_weight)
				continue;

			unit_weight[c] += org_unit_weight[c];

			if (sat_count[c] < clause_true_lit_thres[c])
			{
				for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
				{
					sscore[v] += org_unit_weight[c];
					// min(clause_true_lit_thres[c] - sat_count[c], weight);
					if (score[v] + coeff * sscore[v] > 0 && already_in_goodvar_stack[v] == -1)
					{
						already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
						mypush(v, goodvar_stack);
					}
				}
			}
			else if (sat_count[c] == 1)
			{
				for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
				{
					// weight = p->weight;
					// sscore[v] += org_unit_weight[c];
					if (p->sense == cur_soln[v])
					{
						sscore[v] -= org_unit_weight[c];
						if (already_in_goodvar_stack[v] != -1 && score[v] + coeff * sscore[v] <= 0)
						{
							int top_v = mypop(goodvar_stack);
							goodvar_stack[already_in_goodvar_stack[v]] = top_v;
							already_in_goodvar_stack[top_v] = already_in_goodvar_stack[v];
							already_in_goodvar_stack[v] = -1;
						}
					}
				}
			}
		}
	}
	if (num_hclauses > 0)
	{
		ave_hard_weight += (inc_hard_weight / num_hclauses);
		inc_hard_weight %= num_hclauses;
	}
}

// void Satlike::smooth_weights()
// {
// 	int i, clause, v;
// 	int weight;
// 	if (num_sclauses > 0 && soft_unsat_weight < opt_unsat_weight && ave_soft_weight > (total_soft_weight / num_sclauses))
// 	{
// 		ave_soft_weight -= (total_soft_weight / num_sclauses);
// 		inc_hard_weight -= (total_soft_weight / num_sclauses);
// 		if (inc_hard_weight < 0)
// 			inc_hard_weight = 0;
// 		for (int c = 0; c < num_clauses; ++c)
// 		{
// 			if (org_clause_weight[c] == top_clause_weight)
// 			{
// 				if (unit_weight[c] == 1 && sat_count[c] < clause_true_lit_thres[c])
// 					continue;

// 				unit_weight[c]--;
// 				for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
// 				{
// 					weight = p->weight;
// 					if (p->sense == cur_soln[v])
// 					{
// 						if (sat_count[c] - weight < clause_true_lit_thres[c])
// 						{
// 							score[v] += clause_true_lit_thres[c] - sat_count[c] + weight;
// 							if (score[v] + sscore[v] > 0 && already_in_goodvar_stack[v] == -1)
// 							{
// 								already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
// 								mypush(v, goodvar_stack);
// 							}
// 						}
// 					}
// 				}
// 			}
// 			else
// 			{
// 				unit_weight[c]--;
// 				for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
// 				{
// 					weight = p->weight;
// 					if (p->sense == cur_soln[v])
// 					{
// 						if (sat_count[c] - weight < clause_true_lit_thres[c])
// 						{
// 							sscore[v] += clause_true_lit_thres[c] - sat_count[c] + weight;
// 							if (score[v] + sscore[v] > 0 && already_in_goodvar_stack[v] == -1)
// 							{
// 								already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
// 								mypush(v, goodvar_stack);
// 							}
// 						}
// 					}
// 				}
// 			}
// 		}
// 	}
// 	else
// 	{
// 		for (int c = 0; c < num_clauses; ++c)
// 		{
// 			if (org_clause_weight[c] == top_clause_weight)
// 			{
// 				if (unit_weight[c] == 1 && sat_count[c] < clause_true_lit_thres[c])
// 					continue;

// 				unit_weight[c]--;
// 				for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
// 				{
// 					weight = p->weight;
// 					if (p->sense == cur_soln[v])
// 					{
// 						if (sat_count[c] - weight < clause_true_lit_thres[c])
// 						{
// 							score[v] += clause_true_lit_thres[c] - sat_count[c] + weight;
// 							if (score[v] + sscore[v] > 0 && already_in_goodvar_stack[v] == -1)
// 							{
// 								already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
// 								mypush(v, goodvar_stack);
// 							}
// 						}
// 					}
// 				}
// 			}
// 		}
// 	}
// }

void Satlike::update_clause_weights()
{
	/*
	if (((rand() % MY_RAND_MAX_INT) * BASIC_SCALE) < smooth_probability)
	{
		smooth_weights();
	}
	else
	{*/
	increase_weights();
	//}
}

inline void Satlike::unsat(int clause)
{
	if (org_clause_weight[clause] == top_clause_weight)
	{
		index_in_hardunsat_stack[clause] = hardunsat_stack_fill_pointer;
		mypush(clause, hardunsat_stack);
		hard_unsat_nb++;
	}
	else
	{
		index_in_softunsat_stack[clause] = softunsat_stack_fill_pointer;
		mypush(clause, softunsat_stack);
		// soft_unsat_weight += org_clause_weight[clause];
	}
}

inline void Satlike::sat(int clause)
{
	int index, last_unsat_clause;

	if (org_clause_weight[clause] == top_clause_weight)
	{

		last_unsat_clause = mypop(hardunsat_stack);
		index = index_in_hardunsat_stack[clause];
		hardunsat_stack[index] = last_unsat_clause;
		index_in_hardunsat_stack[last_unsat_clause] = index;

		hard_unsat_nb--;
	}
	else
	{
		last_unsat_clause = mypop(softunsat_stack);
		index = index_in_softunsat_stack[clause];
		softunsat_stack[index] = last_unsat_clause;
		index_in_softunsat_stack[last_unsat_clause] = index;

		// soft_unsat_weight -= org_clause_weight[clause];
	}
}

void Satlike::check_new_score()
{
	long long tem_score = 0;
	long long tem_sscore = 0;
	int sense, c, v, i;
	int weight;
	for (v = 1; v <= num_vars; v++)
	{
		tem_score = 0;
		tem_sscore = 0;
		for (i = 0; i < var_lit_count[v]; ++i)
		{
			c = var_lit[v][i].clause_num;
			sense = var_lit[v][i].sense;
			weight = var_lit[v][i].weight;
			if (org_clause_weight[c] == top_clause_weight)
			{
				if (sat_count[c] < clause_true_lit_thres[c])
				{
					if (sense != cur_soln[v])
					{
						tem_score += unit_weight[c] * min(clause_true_lit_thres[c] - sat_count[c], weight);
					}
					else
						tem_score -= unit_weight[c] * weight;
				}
				else if (sat_count[c] >= clause_true_lit_thres[c])
				{
					if (sense == cur_soln[v])
					{
						tem_score -= unit_weight[c] * max(0, clause_true_lit_thres[c] - sat_count[c] + weight);
					}
				}
			}
			else
			{
				if (sat_count[c] < clause_true_lit_thres[c])
				{
					if (sense != cur_soln[v])
					{
						tem_sscore += unit_weight[c] * min(clause_true_lit_thres[c] - sat_count[c], weight);
					}
					else
						tem_sscore -= unit_weight[c] * weight;
				}
				else if (sat_count[c] >= clause_true_lit_thres[c])
				{
					if (sense == cur_soln[v])
					{
						tem_sscore -= unit_weight[c] * max(0, clause_true_lit_thres[c] - sat_count[c] + weight);
					}
				}
			}
		}
		if (tem_score != score[v] || tem_sscore != sscore[v])
		{

			cout << "score is worng in variable " << v << endl;
			cout << "tem_score is " << tem_score << endl;
			cout << "score function is " << score[v] << endl;
			cout << "flip num is " << step << endl;

			for (i = 0; i < var_lit_count[v]; ++i)
			{
				c = var_lit[v][i].clause_num;
				sense = var_lit[v][i].sense;
				weight = var_lit[v][i].weight;
				cout << c << " ";
			}
			cout << endl;
			exit(0);
			break;
		}
	}

	int tem_unsat_softweight = 0;
	for (int i = 0; i < num_clauses; ++i)
	{
		if (org_clause_weight[i] == top_clause_weight)
			continue;
		if (sat_count[i] < clause_true_lit_thres[i])
		{
			tem_unsat_softweight += (clause_true_lit_thres[i] - sat_count[i]);
		}
	}
	if (tem_unsat_softweight != soft_unsat_weight)
	{
		cout << "verify softunsat weight wrong " << endl;
		exit(0);
	}
}

int UP(int &new_num_vars, int &new_num_clauses, const ll top_clause_weight, ll *&new_org_clause_weight,
       int *&new_clause_lit_count, int *&new_clause_true_lit_thres, lit **&new_clause_lit,
       ll &wecnf_obj_pre, ll &real_obj_pre, int *&fix_var)
{
	// printf("UP with Literal assume %d,%d\n", la_idx, la_val);
    vector<ll> sum_left(ori_clause_num);
    vector<int> queue_idx;
    vector<int> queue_val;
    vector<int> scan_idx(ori_clause_num);
    for (int i = 1; i <= ori_var_num; ++i) fix_var[i] = -1;
    if (la_idx != -1) {
        queue_idx.reserve(1000);
        queue_val.reserve(1000);
        queue_idx.push_back(la_idx);
        queue_val.push_back(la_val);
        fix_var[la_idx] = la_val;
    }
    for (int c = 0; c < ori_clause_num; ++c)
    {
        scan_idx[c] = ori_clause_lit_count[c] - 1;
        sum_left[c] = 0;
        for (int j = 0; j < ori_clause_lit_count[c]; ++j)
            sum_left[c] += ori_clause_lit[c][j].weight;
    }
    for (int c = 0; c < ori_clause_num; ++c)
    {
		new_clause_true_lit_thres[c] = ori_clause_true_lit_thres[c];
        if (ori_org_clause_weight[c] != top_clause_weight)
            continue;
        for (int j = scan_idx[c]; j >= 0; --j)
            if (sum_left[c] - ori_clause_lit[c][j].weight + 1 <= new_clause_true_lit_thres[c])
            {
                if (fix_var[ori_clause_lit[c][j].var_num] == -1)
                {
					// printf("%d = %d\n", ori_clause_lit[c][j].var_num, ori_clause_lit[c][j].sense);
                    queue_idx.push_back(ori_clause_lit[c][j].var_num);
                    queue_val.push_back(ori_clause_lit[c][j].sense);
                    fix_var[ori_clause_lit[c][j].var_num] = ori_clause_lit[c][j].sense;
                    scan_idx[c] = j - 1;
                }
                else if (fix_var[ori_clause_lit[c][j].var_num] != ori_clause_lit[c][j].sense)
                    return -1;
            }
            else
                break;
    }
    if (queue_idx.size() == 0) {
		
    	// printf("new_num_vars: %d,prs.ori_var_num: %d,new_num_clauses: %d,prs.ori_clause_num: %d\n",
        //    ori_var_num, ori_var_num, ori_clause_num, ori_clause_num);
		return 0;
	}
    while (queue_idx.size() > 0)
    {
        int idx = queue_idx[queue_idx.size() - 1];
        int val = queue_val[queue_idx.size() - 1];
        queue_idx.pop_back();
        queue_val.pop_back();
        for (int i = 0; i < watch[idx].size(); i++)
        {
            lit now_lit = watch[idx][i];
            int c = now_lit.clause_num;
            if (now_lit.sense == val)
            {
                sum_left[c] -= now_lit.weight;
                new_clause_true_lit_thres[c] -= now_lit.weight;
            }
            else
                sum_left[c] -= now_lit.weight;
            if (ori_org_clause_weight[c] != top_clause_weight)
                continue;
            for (int j = scan_idx[c]; j >= 0; --j)
            {
                if (ori_clause_lit[c][j].var_num == idx)
                    continue;
				// if (la_val == 1) printf("%d %d %d\n", c, j, ori_clause_lit[c][j].var_num);
                if (fix_var[ori_clause_lit[c][j].var_num] != -1)
                    continue;
                if (sum_left[c] - ori_clause_lit[c][j].weight + 1 <= new_clause_true_lit_thres[c])
                {
                    if (fix_var[ori_clause_lit[c][j].var_num] == -1)
                    {
                        queue_idx.push_back(ori_clause_lit[c][j].var_num);
                        queue_val.push_back(ori_clause_lit[c][j].sense);
                        fix_var[ori_clause_lit[c][j].var_num] = ori_clause_lit[c][j].sense;
                        scan_idx[c] = j - 1;
                    }
                    else if (fix_var[ori_clause_lit[c][j].var_num] != ori_clause_lit[c][j].sense)
                        return -1;
                }
                else
                    break;
            }
        }
    }
    // 删数据，重标号
    new_num_vars = ori_var_num;
    for (int i = 1; i <= ori_var_num; ++i)
        new_num_vars -= (fix_var[i] != -1);
    new_num_clauses = ori_clause_num;
    for (int c = 0; c < ori_clause_num; ++c)
        new_num_clauses -= (new_clause_true_lit_thres[c] <= 0) || (sum_left[c] < new_clause_true_lit_thres[c]);
    int *old_new_var = new int[ori_var_num + 10];
    int *new_old_clause = new int[ori_clause_num + 10];
    int new_idx = 1;
    int old_idx = 1;
    while (old_idx <= ori_var_num)
        if (fix_var[old_idx] == -1)
        {
            old_new_var[old_idx] = new_idx;
            new_idx++;
            old_idx++;
        }
        else
            old_idx++;
    assert(new_idx == new_num_vars + 1);
    new_idx = 0;
    old_idx = 0;
    while (old_idx < ori_clause_num)
    {
        if (ori_org_clause_weight[old_idx] == top_clause_weight)
        {
            // printf("sum_left[old_idx] < new_clause_true_lit_thres[old_idx]: %d", sum_left[old_idx] < new_clause_true_lit_thres[old_idx]);
            if (sum_left[old_idx] < new_clause_true_lit_thres[old_idx])
            {
                // printf("%d\n", old_idx);
                return -1;
            }

            if (new_clause_true_lit_thres[old_idx] > 0)
            {
                new_old_clause[new_idx] = old_idx;
                new_idx++;
                old_idx++;
            }
            else
                old_idx++;
        }
        else
        {
            if (sum_left[old_idx] < new_clause_true_lit_thres[old_idx])
            {
                // unsat
                wecnf_obj_pre += ori_org_clause_weight[old_idx];
                if (fix_var[ori_clause_lit[old_idx][0].var_num] == 1)
                    real_obj_pre += ori_org_clause_weight[old_idx] * (ori_clause_lit[old_idx][0].sense == 1 ? -1 : 1);
                old_idx++;
            }
            else if (new_clause_true_lit_thres[old_idx] <= 0)
            {
                // sat
                if (fix_var[ori_clause_lit[old_idx][0].var_num] == 1)
                    real_obj_pre += ori_org_clause_weight[old_idx] * (ori_clause_lit[old_idx][0].sense == 1 ? -1 : 1);
                old_idx++;
            }
            else
            {
                // unfix
                new_old_clause[new_idx] = old_idx;
                new_idx++;
                old_idx++;
            }
        }
    }
    assert(new_idx == new_num_clauses);
    int total_lits = 0;
    for (int c = 0; c < new_num_clauses; c++)
    {
        int old_c = new_old_clause[c];
        for (int v = 0; v < ori_clause_lit_count[old_c]; v++)
            if (fix_var[ori_clause_lit[old_c][v].var_num] == -1)
                ++total_lits;
        ++total_lits;
    }
    lit *space = new lit[total_lits];
    int total_id = 0;
    for (int c = 0; c < new_num_clauses; c++)
    {
        int old_c = new_old_clause[c];
        new_org_clause_weight[c] = ori_org_clause_weight[old_c];
        new_clause_lit_count[c] = ori_clause_lit_count[old_c];
		// printf("%d %d\n", c, new_clause_lit_count[c]);
        new_clause_true_lit_thres[c] = new_clause_true_lit_thres[old_c];
        new_idx = 0;
        old_idx = 0;
        // new_clause_lit[c] = new lit[prs.clause_lit_count[old_c] + 1];
        new_clause_lit[c] = &space[total_id];
        while (old_idx < ori_clause_lit_count[old_c])
        {
            if (fix_var[ori_clause_lit[old_c][old_idx].var_num] == -1)
            {
                new_clause_lit[c][new_idx].clause_num = c;
                new_clause_lit[c][new_idx].var_num = old_new_var[ori_clause_lit[old_c][old_idx].var_num];
                assert(new_clause_lit[c][new_idx].var_num > 0);
                new_clause_lit[c][new_idx].weight = ori_clause_lit[old_c][old_idx].weight;
                new_clause_lit[c][new_idx].sense = ori_clause_lit[old_c][old_idx].sense;
                new_idx++;
                total_id++;
            }
            old_idx++;
        }
        new_clause_lit[c][new_idx].var_num = 0;
        new_clause_lit[c][new_idx].clause_num = -1;
        new_clause_lit[c][new_idx].weight = 0;
        new_clause_lit_count[c] = new_idx;
        total_id++;
        assert(new_idx != 0);
    }
    assert(total_id == total_lits);
    printf("new_num_vars: %d,prs.ori_var_num: %d,new_num_clauses: %d,prs.ori_clause_num: %d\n",
           new_num_vars, ori_var_num, new_num_clauses, ori_clause_num);
    return 1;
}

void read_wecnf(char *filename)
{
    istringstream iss;
    char line[1024];
    string line2;
    char tempstr1[10];
    char tempstr2[10];
    int i, v, c;
    ifstream infile(filename);
    if (!infile)
    {
        printf("c the input filename %s is invalid, please input the correct filename.\n", filename);
        exit(-1);
    }
    getline(infile, line2);
    while (line2[0] != 'p')
        getline(infile, line2);
    for (i = 0; i < 1024; i++)
        line[i] = line2[i];
    sscanf(line, "%s %s %d %d %lld", tempstr1, tempstr2, &num_vars, &num_clauses, &top_clause_weight);
    ori_org_clause_weight = new long long[num_clauses + 10];
    ori_clause_true_lit_thres = new int[num_clauses + 10];
    ori_clause_lit_count = new int[num_clauses + 10];
    ori_clause_lit = new lit *[num_clauses + 10];
    vector<pair<int, int>> temp_weight_lit;
    temp_weight_lit.reserve(num_vars + 10);
    int cur_weight;
    int cur_lit;
    c = 0;
    while (getline(infile, line2))
    {
        if (line2[0] == 'c')
            continue;
        else
        {
            iss.clear();
            iss.str(line2);
            iss.seekg(0, ios::beg);
        }
        ori_clause_lit_count[c] = 0;
        temp_weight_lit.clear();
        iss >> ori_org_clause_weight[c];
        iss >> ori_clause_true_lit_thres[c];
        iss >> cur_weight;
        iss >> cur_lit;
        while (cur_weight != 0)
        {
            temp_weight_lit.push_back(make_pair(cur_weight, cur_lit));
            ori_clause_lit_count[c]++;
            iss >> cur_weight;
            iss >> cur_lit;
        }
        assert(temp_weight_lit.size() == ori_clause_lit_count[c]);
        std::sort(temp_weight_lit.begin(), temp_weight_lit.end(), std::less<std::pair<int, int>>());
        ori_clause_lit[c] = new lit[ori_clause_lit_count[c] + 1];
        for (i = 0; i < ori_clause_lit_count[c]; ++i)
        {
            ori_clause_lit[c][i].clause_num = c;
            ori_clause_lit[c][i].var_num = abs(temp_weight_lit[i].second);
            ori_clause_lit[c][i].weight = temp_weight_lit[i].first;
            if (temp_weight_lit[i].second > 0)
                ori_clause_lit[c][i].sense = 1;
            else
                ori_clause_lit[c][i].sense = 0;
        }
        ori_clause_lit[c][i].var_num = 0;
        ori_clause_lit[c][i].clause_num = -1;
        ori_clause_lit[c][i].weight = 0;
        c++;
    }
    infile.close();
    watch.resize(num_vars + 1);
    for (int c = 0; c < num_clauses; ++c)
        for (int j = 0; j < ori_clause_lit_count[c]; ++j)
            watch[ori_clause_lit[c][j].var_num].push_back(ori_clause_lit[c][j]);
    ori_var_num = num_vars;
    ori_clause_num = num_clauses;
	
    org_clause_weight = new long long[num_clauses + 10];
    clause_true_lit_thres = new int[num_clauses + 10];
    clause_lit_count = new int[num_clauses + 10];
}

int doup(Satlike *p) {
	fix_var = new int[ori_var_num + 10];
	num_vars = ori_var_num;
	num_clauses = ori_clause_num;
	
    p->clause_lit = new lit *[ori_clause_num + 10];
	p->org_clause_weight = new long long[ori_clause_num + 10];
    p->clause_true_lit_thres = new int[ori_clause_num + 10];
    p->clause_lit_count = new int[ori_clause_num + 10];
	for (int c = 0; c < ori_clause_num; c++)
    {
        p->clause_lit_count[c] = 0;
        p->clause_true_lit_thres[c] = 1;
        p->clause_lit[c] = NULL;
    }
	p->wecnf_obj_pre = 0;
	p->real_obj_pre = 0;
	int res = UP(num_vars, num_clauses, top_clause_weight, org_clause_weight,
					clause_lit_count, clause_true_lit_thres, p->clause_lit,
					p->wecnf_obj_pre, p->real_obj_pre, fix_var);

	printf("UP result: %d\n-----------------------\n", res);
	if (res == -1) return 0;
	else if (res == 0)
	{
		for (int c = 0; c < num_clauses; c++) {
			clause_lit_count[c] = ori_clause_lit_count[c];
			org_clause_weight[c] = ori_org_clause_weight[c];
			clause_true_lit_thres[c] = ori_clause_true_lit_thres[c];
		}	
		int total_lits = 0;
		for (int c = 0; c < num_clauses; c++)
			total_lits += clause_lit_count[c] + 1;
		lit *space = new lit[total_lits];
		int total_id = 0;
		for (int c = 0; c < num_clauses; c++)
		{
			p->clause_lit[c] = &space[total_id];
			for (int i = 0; i <= clause_lit_count[c]; ++i)
			{
				p->clause_lit[c][i].clause_num = ori_clause_lit[c][i].clause_num;
				p->clause_lit[c][i].var_num = ori_clause_lit[c][i].var_num;
				p->clause_lit[c][i].weight = ori_clause_lit[c][i].weight;
				p->clause_lit[c][i].sense = ori_clause_lit[c][i].sense;
				// printf("%d ", p->clause_lit[c][i].var_num);
			}
			// printf("%d\n", clause_true_lit_thres[c]);
			total_id += clause_lit_count[c] + 1;
		}
		assert(total_id == total_lits);
	}
	
	
	// down is PRS 
    p->num_vars = num_vars;
    p->num_clauses = num_clauses;
    p->top_clause_weight = top_clause_weight;
    for (int c = 0; c < num_clauses; c++)
    {
        p->clause_lit_count[c] = clause_lit_count[c];
        p->org_clause_weight[c] = org_clause_weight[c];
        p->clause_true_lit_thres[c] = clause_true_lit_thres[c];
    }
    p->build_instance();
	return 1;
}



int main(int argc, char *argv[])
{

	int rseed = 0;
	srand(rseed);

	start_timing();

	Satlike *s = new Satlike();

	s->cutoff_time = atoi(argv[2]);
	s->coeff_inc = s->coeff_dec = atof(argv[3]);
	s->adjust_rounds = atoi(argv[4]);

	read_wecnf(argv[1]);
	int res = doup(s);
	if (res == 0) {
		printf("infeasible.\n");
		printf("U\t no feasible solution\n");
		exit(0);
	}
	ll wecnf_res = 1e18;
	ll real_res = 1e18;
	double opttime;
	int tries;
	if (ori_clause_num <= 10000) {
		while (true) {
			vector<int> init_solution;
			int res = s->local_search_with_decimation(init_solution, 1);
			if (s->best_soln_feasible == 1 && s->opt_unsat_weight + s->wecnf_obj_pre < wecnf_res) {
				assert(s->opt_real_weight + s->real_obj_pre < real_res);
				wecnf_res = s->opt_unsat_weight + s->wecnf_obj_pre;
				real_res = s->opt_real_weight + s->real_obj_pre;
				// printf("=========== better %lld %lld\n", wecnf_res, real_res);
				opttime = s->opt_time;
				tries = s->tries;
			}
			s->free_memory();
			if (res == 1 || res == -1) break;
			int times=0;
			do {
				delete s;
				s = new Satlike();
				s->cutoff_time = atoi(argv[2]);
				s->coeff_inc = atof(argv[3]);
				s->coeff_dec = atof(argv[4]);
				s->adjust_rounds = atoi(argv[5]);
				if (la_idx == -1) la_idx = rand() % ori_var_num + 1, la_val = 0;
				else if (la_val == 0) la_val = 1;
				else la_idx = rand() % ori_var_num + 1, la_val = 0;
				if (++times >= 100) {la_idx = -1, la_val = 0;}
				int res = doup(s);
				if (res == 1) break;
			} while (true);
		}
		if (wecnf_res != 1e18)
			cout << "B\t" << wecnf_res << '\t' << real_res
				<< '\t' << opttime << '\t' << tries << '\t' << endl;
		else
			cout << "U\t no feasible solution" << endl;
	}
	else {	
		vector<int> init_solution;
		s->local_search_with_decimation(init_solution, 0);
		//s.simple_print();
		s->print_best_solution();
		s->free_memory();
	}
	return 0;
}
