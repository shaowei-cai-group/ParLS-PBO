
#include <cmath>
#include <cassert>
#include "basis_pms.h"
#include <sstream>
#include <algorithm>
#include <chrono>

Satlike::Satlike()
{
	/**********PRS added************/
	terminated = 0;
	best_flips = 0;
	cccheck = 1;
	wecnf_obj_pre = 0;
	real_obj_pre = 0;

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
	softclause_weight_threshold = 1;

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
	time_stamp = new long long[malloc_var_length];

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
	for (i = 0; i < num_clauses; i++)
		delete[] clause_lit[i];

	delete[] var_lit;
	delete[] var_lit_count;
	delete[] clause_lit;
	delete[] clause_lit_count;
	delete[] clause_true_lit_thres;

	delete[] score;
	delete[] oscore;
	delete[] sscore;
	delete[] time_stamp;

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

		for (i = 0; i < clause_lit_count[c]; ++i)
			var_lit_count[clause_lit[c][i].var_num]++;

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
	best_soln_feasible = 0;
	opt_unsat_weight = total_soft_weight + 1;
}

void Satlike::init(vector<int> &init_solution, int sharing)
{
	int v, c;
	int j;

	if (init_sharing == 0)
	{
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
	}
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
				cur_soln[v] = rand_r(&seed) % 2;
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
	bool no_use_gs = rand_r(&seed) % 100 >= gs_prob;
	if (goodvar_stack_fill_pointer > 0)
	{
		if ((rand_r(&seed) % MY_RAND_MAX_INT) * BASIC_SCALE < rdprob)
			return goodvar_stack[rand_r(&seed) % goodvar_stack_fill_pointer];

		if (goodvar_stack_fill_pointer < hd_count_threshold)
		{
			best_var = goodvar_stack[0];
			double global_score_best_var = cur_soln[best_var] == 0 ? global_score_1[new_old_var[best_var]] : global_score_0[new_old_var[best_var]];
			if(no_use_gs)
				global_score_best_var = 1;
			for (i = 1; i < goodvar_stack_fill_pointer; ++i)
			{
				v = goodvar_stack[i];
				double global_score_v = cur_soln[v] == 0 ? global_score_1[new_old_var[v]] : global_score_0[new_old_var[v]];
				if(no_use_gs)
					global_score_v = 1;
				if ((score[v] + coeff * sscore[v]) * global_score_v > (score[best_var] + coeff * sscore[best_var]) * global_score_best_var)
				{
					best_var = v;
					global_score_best_var = global_score_v;
				}
				else if ((score[v] + coeff * sscore[v]) * global_score_v == (score[best_var] + coeff * sscore[best_var]) * global_score_best_var)
				{
					if (time_stamp[v] < time_stamp[best_var])
					{
						best_var = v;
						global_score_best_var = global_score_v;
					}
				}
			}
			// printf("c global_score_best_var:%f\n", global_score_best_var);
			return best_var;
		}
		else
		{

			int r = rand_r(&seed) % goodvar_stack_fill_pointer;
			best_var = goodvar_stack[r];
			double global_score_best_var = cur_soln[best_var] == 0 ? global_score_1[new_old_var[best_var]] : global_score_0[new_old_var[best_var]];
			if(no_use_gs)
				global_score_best_var = 1;
			for (i = 1; i < hd_count_threshold; ++i)
			{
				r = rand_r(&seed) % goodvar_stack_fill_pointer;
				v = goodvar_stack[r];
				double global_score_v = cur_soln[v] == 0 ? global_score_1[new_old_var[v]] : global_score_0[new_old_var[v]];
				if(no_use_gs)
					global_score_v = 1;
				if ((score[v] + coeff * sscore[v]) * global_score_v > (score[best_var] + coeff * sscore[best_var]) * global_score_best_var)
				{
					best_var = v;
					global_score_best_var = global_score_v;
				}
				else if ((score[v] + coeff * sscore[v]) * global_score_v == (score[best_var] + coeff * sscore[best_var]) * global_score_best_var)
				{
					if (time_stamp[v] < time_stamp[best_var])
					{
						best_var = v;
						global_score_best_var = global_score_v;
					}
				}
			}
			// printf("c global_score_best_var:%f\n", global_score_best_var);
			return best_var;
		}
	}
	update_clause_weights();
	int sel_c;
	lit *p;

	if (hardunsat_stack_fill_pointer > 0)
	{
		sel_c = hardunsat_stack[rand_r(&seed) % hardunsat_stack_fill_pointer];
	}
	else
	{
		sel_c = softunsat_stack[rand_r(&seed) % softunsat_stack_fill_pointer];
	}
	if ((rand_r(&seed) % MY_RAND_MAX_INT) * BASIC_SCALE < rwprob)
		return clause_lit[sel_c][rand_r(&seed) % clause_lit_count[sel_c]].var_num;
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
	// for (int index = goodvar_stack_fill_pointer - 1; index >= 0; index--)
	// {
	// 	v = goodvar_stack[index];
	// 	if (score[v] + coeff * sscore[v] <= 0)
	// 	{
	// 		printf("%d %d Wrong", v, flipvar);
	// 		int top_v = mypop(goodvar_stack);
	// 		goodvar_stack[index] = top_v;
	// 		already_in_goodvar_stack[top_v] = index;
	// 		already_in_goodvar_stack[v] = -1;
	// 	}
	// }

	if (cccheck == 0 && score[flipvar] + coeff * sscore[flipvar] > 0 && already_in_goodvar_stack[flipvar] == -1)
	{
		already_in_goodvar_stack[flipvar] = goodvar_stack_fill_pointer;
		mypush(flipvar, goodvar_stack);
	}
}

void Satlike::flip(int flipvar)
{
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
							if (score[v] + coeff * sscore[v] <= 0 && already_in_goodvar_stack[v] != -1) {
								int index = already_in_goodvar_stack[v];
								int top_v = mypop(goodvar_stack);
								goodvar_stack[index] = top_v;
								already_in_goodvar_stack[top_v] = index;
								already_in_goodvar_stack[v] = -1;
							}
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
							if (score[v] + coeff * sscore[v] <= 0 && already_in_goodvar_stack[v] != -1) {
								int index = already_in_goodvar_stack[v];
								int top_v = mypop(goodvar_stack);
								goodvar_stack[index] = top_v;
								already_in_goodvar_stack[top_v] = index;
								already_in_goodvar_stack[v] = -1;
							}
						}
						else
						{
							score[v] += unit_weight[c] * (p->weight - max(0, gap - weight + p->weight));
							if (score[v] + coeff * sscore[v] > 0 && already_in_goodvar_stack[v] == -1 && v != flipvar)
							{
								already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
								mypush(v, goodvar_stack);
							}
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
							if (score[v] + coeff * sscore[v] > 0 && already_in_goodvar_stack[v] == -1 && v != flipvar)
							{
								already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
								mypush(v, goodvar_stack);
							}
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
							if (score[v] + coeff * sscore[v] <= 0 && already_in_goodvar_stack[v] != -1) {
								int index = already_in_goodvar_stack[v];
								int top_v = mypop(goodvar_stack);
								goodvar_stack[index] = top_v;
								already_in_goodvar_stack[top_v] = index;
								already_in_goodvar_stack[v] = -1;
							}
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
							if (score[v] + coeff * sscore[v] <= 0 && already_in_goodvar_stack[v] != -1) {
								int index = already_in_goodvar_stack[v];
								int top_v = mypop(goodvar_stack);
								goodvar_stack[index] = top_v;
								already_in_goodvar_stack[top_v] = index;
								already_in_goodvar_stack[v] = -1;
							}
						}
						else
						{
							score[v] += unit_weight[c] * min(p->weight, gap + weight);
							if (score[v] + coeff * sscore[v] > 0 && already_in_goodvar_stack[v] == -1 && v != flipvar)
							{
								already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
								mypush(v, goodvar_stack);
							}
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
							if (score[v] + coeff * sscore[v] > 0 && already_in_goodvar_stack[v] == -1 && v != flipvar)
							{
								already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
								mypush(v, goodvar_stack);
							}
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
							if (score[v] + coeff * sscore[v] <= 0 && already_in_goodvar_stack[v] != -1) {
								int index = already_in_goodvar_stack[v];
								int top_v = mypop(goodvar_stack);
								goodvar_stack[index] = top_v;
								already_in_goodvar_stack[top_v] = index;
								already_in_goodvar_stack[v] = -1;
							}
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
							if (score[v] + coeff * sscore[v] <= 0 && already_in_goodvar_stack[v] != -1) {
								int index = already_in_goodvar_stack[v];
								int top_v = mypop(goodvar_stack);
								goodvar_stack[index] = top_v;
								already_in_goodvar_stack[top_v] = index;
								already_in_goodvar_stack[v] = -1;
							}
						}
						else
						{
							sscore[v] += unit_weight[c] * (p->weight - max(0, gap - weight + p->weight));
							if (score[v] + coeff * sscore[v] > 0 && already_in_goodvar_stack[v] == -1 && v != flipvar)
							{
								already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
								mypush(v, goodvar_stack);
							}
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
							if (score[v] + coeff * sscore[v] > 0 && already_in_goodvar_stack[v] == -1 && v != flipvar)
							{
								already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
								mypush(v, goodvar_stack);
							}
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
							if (score[v] + coeff * sscore[v] <= 0 && already_in_goodvar_stack[v] != -1) {
								int index = already_in_goodvar_stack[v];
								int top_v = mypop(goodvar_stack);
								goodvar_stack[index] = top_v;
								already_in_goodvar_stack[top_v] = index;
								already_in_goodvar_stack[v] = -1;
							}
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
							if (score[v] + coeff * sscore[v] <= 0 && already_in_goodvar_stack[v] != -1) {
								int index = already_in_goodvar_stack[v];
								int top_v = mypop(goodvar_stack);
								goodvar_stack[index] = top_v;
								already_in_goodvar_stack[top_v] = index;
								already_in_goodvar_stack[v] = -1;
							}
						}
						else
						{
							sscore[v] += unit_weight[c] * min(p->weight, gap + weight);
							if (score[v] + coeff * sscore[v] > 0 && already_in_goodvar_stack[v] == -1 && v != flipvar)
							{
								already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
								mypush(v, goodvar_stack);
							}
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
							if (score[v] + coeff * sscore[v] > 0 && already_in_goodvar_stack[v] == -1 && v != flipvar)
							{
								already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
								mypush(v, goodvar_stack);
							}
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
	v = flipvar;
	if (score[v] + coeff * sscore[v] <= 0 && already_in_goodvar_stack[v] != -1) {
		int index = already_in_goodvar_stack[v];
		int top_v = mypop(goodvar_stack);
		goodvar_stack[index] = top_v;
		already_in_goodvar_stack[top_v] = index;
		already_in_goodvar_stack[v] = -1;
	}
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

int Satlike::local_search_with_decimation(vector<int> &init_solution)
{
	// printf("local_search_with_decimation...\n");
	settings();
	sharing_i = 0;
	punish_i = 0;
	restart_i = 0;
	init_sharing = 0;
	for (tries = 1; tries < max_tries; ++tries)
	{
		init(init_solution, init_sharing);
		init_sharing = 0;
		restart_i = 0;
		for (step = 1; step < max_flips; ++step)
		{		
			if (terminated)
			{
				printf("c	tries: %d, step: %d, ceoff = %.2lf\n", tries, step, coeff);
				return 0;
			}
			if (hard_unsat_nb == 0) feasibles = 1; // can if (hard == 0 && last_find_feasible_step<= step - K)
			if (hard_unsat_nb == 0 && cbkUpdateRecent != NULL)
			{
				int res = cbkUpdateRecent(issuer, soft_unsat_weight + wecnf_obj_pre, cur_soln, num_vars);
				// printf("c cbkUpdateRecent (%lld), (%lld), (%d)\n", opt_unsat_weight, soft_unsat_weight, res);
				punish_i = res ? 0 : punish_i;
			}
			if (hard_unsat_nb == 0 && (soft_unsat_weight < opt_unsat_weight || best_soln_feasible == 0))
			{
				// cout << "unsat soft stack fill pointer" << softunsat_stack_fill_pointer << endl;
				if (soft_unsat_weight < top_clause_weight)
				{
					// 记录一下当前step
					softclause_weight_threshold += 0;
					best_soln_feasible = 1;
					opt_unsat_weight = soft_unsat_weight;
					for (int v = 1; v <= num_vars; ++v)
						best_soln[v] = cur_soln[v];
					best_flips = step;

					long long real_weight = cal_opb_weight();
					opt_real_weight = real_weight;
					cbkUpdateSolution(issuer, opt_unsat_weight + wecnf_obj_pre, cur_soln, num_vars, opt_real_weight + real_obj_pre);
					// simple_print();
					// printf("%lld %lld\n", opt_unsat_weight, real_weight);
					if ((opt_unsat_weight + wecnf_obj_pre) == 0 ||
						(opt_real_weight + real_obj_pre) == opt_result && opt_result != (long long)(1e18))
						return 1;
					if (opt_unsat_weight == 0)
						return 2;
					sharing_i = 0;
					restart_i = 0;
					punish_i = 0;
				}
			}
			if (sharing_period != -1 && sharing_i > sharing_period && cbkGetOtherModel != NULL)
			{
				sharing_i = 0;
				int res = cbkGetOtherModel(issuer, num_vars, soft_unsat_weight + wecnf_obj_pre, cur_soln);
				if (res >= 0)
				{
					init_sharing = 1;
					break;
				}
			}
			if (punish_period != -1 && punish_i > punish_period && cbkPunish != NULL)
			{
				punish_i = 0;
				cbkPunish(issuer);
			}
			if (restart_period != -1 && restart_i > restart_period)
			{
				restart_i = 0;
				for (int i = 1; i <= num_vars; i++)
					init_solution[i] = rand_r(&seed) % 2;
				break;
			}
			if (step % adjust_rounds == 0) {
				// printf("step %d, coeff: %.2lf -> ", step, coeff);
				if (feasibles) coeff *= coeff_inc;
				else coeff /= coeff_dec;
				coeff = max(coeff, 0.46006168878974407);
				coeff = min(coeff, 50.0);
				// printf("%.2lf\n", coeff);
				feasibles = 0;
				// adjust_good_var();
			}
			int flipvar = pick_var();
			flip(flipvar);
			// check_new_score();
			time_stamp[flipvar] = step;
			sharing_i++;
			restart_i++;
			punish_i++;
		}
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
			cout << opt_unsat_weight << '\t' << opt_real_weight << '\t' << opt_time << '\t' << tries << '\t' << seed << '\t' << endl;
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

void Satlike::smooth_weights()
{
	int i, clause, v;
	int weight;
	if (num_sclauses > 0 && soft_unsat_weight < opt_unsat_weight && ave_soft_weight > (total_soft_weight / num_sclauses))
	{
		ave_soft_weight -= (total_soft_weight / num_sclauses);
		inc_hard_weight -= (total_soft_weight / num_sclauses);
		if (inc_hard_weight < 0)
			inc_hard_weight = 0;
		for (int c = 0; c < num_clauses; ++c)
		{
			if (org_clause_weight[c] == top_clause_weight)
			{
				if (unit_weight[c] == 1 && sat_count[c] < clause_true_lit_thres[c])
					continue;

				unit_weight[c]--;
				for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
				{
					weight = p->weight;
					if (p->sense == cur_soln[v])
					{
						if (sat_count[c] - weight < clause_true_lit_thres[c])
						{
							score[v] += clause_true_lit_thres[c] - sat_count[c] + weight;
							if (score[v] + coeff * sscore[v] > 0 && already_in_goodvar_stack[v] == -1)
							{
								already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
								mypush(v, goodvar_stack);
							}
						}
					}
				}
			}
			else
			{
				unit_weight[c]--;
				for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
				{
					weight = p->weight;
					if (p->sense == cur_soln[v])
					{
						if (sat_count[c] - weight < clause_true_lit_thres[c])
						{
							sscore[v] += clause_true_lit_thres[c] - sat_count[c] + weight;
							if (score[v] + coeff * sscore[v] > 0 && already_in_goodvar_stack[v] == -1)
							{
								already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
								mypush(v, goodvar_stack);
							}
						}
					}
				}
			}
		}
	}
	else
	{
		for (int c = 0; c < num_clauses; ++c)
		{
			if (org_clause_weight[c] == top_clause_weight)
			{
				if (unit_weight[c] == 1 && sat_count[c] < clause_true_lit_thres[c])
					continue;

				unit_weight[c]--;
				for (lit *p = clause_lit[c]; (v = p->var_num) != 0; p++)
				{
					weight = p->weight;
					if (p->sense == cur_soln[v])
					{
						if (sat_count[c] - weight < clause_true_lit_thres[c])
						{
							score[v] += clause_true_lit_thres[c] - sat_count[c] + weight;
							if (score[v] + coeff * sscore[v] > 0 && already_in_goodvar_stack[v] == -1)
							{
								already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
								mypush(v, goodvar_stack);
							}
						}
					}
				}
			}
		}
	}
}

void Satlike::update_clause_weights()
{
	/*
	if (((rand_r(&seed) % MY_RAND_MAX_INT) * BASIC_SCALE) < smooth_probability)
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
