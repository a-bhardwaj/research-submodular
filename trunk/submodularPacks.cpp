// -------------------------------------------------------------- -*- C++ -*-
// File: subModularKnapsack.cpp
// @author: Avinash Bhardwaj
// --------------------------------------------------------------------------
// Property of Berkeley Computational Optimization Group,
// University of California, Berkeley
// --------------------------------------------------------------------------
//
// subModularKnapsack.cpp - Performance testing of the pack and extended pack
//							inequalities against the CPLEX 12.3 standard and
//							outer approximation procedures for submodular knap-
//							sack problem with non-increasing set functions.

/*
REMARK :					To check if an array contains integers do 
							arrayName.areElementsInteger();

REMARK :					Never use IloCplex::getCplexTime() to measure solve
							time. It returns the time elapsed since the start of
							the application and thus will keep increasing.

REMARK :					As soon as you apply any control callbacks cplex by 
							default turn offs the parallel processing of the nodes 
							to avoid any logical misinterpretation. This can be 
							turned back again by threads Parameter of the IloCplex 
							Object For eg: IloCplex::setParam((IloCplex::Threads, N)), 
							where N is the minimum of the number of parallel licences 
							available and number of parallel processing threads on 
							the machine. For more information refer to Parameters Manual 
							of your CPLEX version for Parameter name 
							"global default thread count"
*/


#include <ilcplex/ilocplex.h>
#include <time.h>

ILOSTLBEGIN

#define EPSILON 1e-4

typedef IloArray<IloIntArray>    IntMatrix;
typedef IloArray<IloNumVarArray> NumVarMatrix;

void 
	usage(const char* name) {
		cerr << endl;
		cerr << "usage:   " << name << " <input file>" <<  " <output file>" << endl;
		cerr << endl;
}

IloIntArray 
	findIndices(IloNumArray binaryArray) {
		IloEnv env = binaryArray.getEnv();
		IloIntArray indices(env,IloSum(binaryArray));
		int l=0;
		for(int i = 0; i < binaryArray.getSize(); i++){
			if(binaryArray[i] == 1){
				indices[l] = i;
				l++;
			}
		}
		return indices;
}

IloNum 
	f(IloNumArray	arcs,
	  IloNumArray	a,
	  IloNumArray	d_sq,
	  IloNum		omega) {
	
	IloNum value = 0;
	value = IloScalProd(arcs,a) + omega*sqrt(IloScalProd(arcs,d_sq));
	return value;
}

IloNumArray
	getComplement(IloNumArray binaryArray) {
		IloEnv env = binaryArray.getEnv();
		IloNumArray binaryArrayComp(env, binaryArray.getSize());
		
		for (int i = 0; i < binaryArray.getSize(); i++)
			binaryArrayComp[i] = 1 - binaryArray[i];

		return binaryArrayComp;
}

bool
	alreadyExists(IloNumArray	pack,
				  IloNumArray2	packs) {
	
	IloEnv env = packs.getEnv();
	bool isSame = false;
	int nRows = packs.getSize(), nCols;
	if (nRows > 0){
			nCols =  packs[0].getSize();
	}
	for (int i = 0; i < nRows; i++) {
		for (int j = 0; j < nCols; j++) {
			if (pack[j] == packs[i][j]) {
				isSame = true;
			}
			else {
				isSame = false;
				break;
			}
		}
		if(isSame){
			break;
		}
	}

	return isSame;
}

IloNumArray
	getRow(IloNumArray2 matrix,
		   IloInt		rowId) {
	IloEnv env = matrix.getEnv();
	int i, n = matrix[0].getSize();
	IloNumArray vector(env, n);

	for (i = 0; i < n; i++)
		vector[i] = matrix[rowId][i];

	return vector;
}

IloNumArray2
	getPack(IloNumArray		a,
			IloNumArray		d,
			IloNum			b,
			IloNum			omega,
			IloNumArray		xbar,
			IloNumArray2	packs) {

	int i;
	IloEnv		env			= a.getEnv();
	IloNum		nCols		= a.getSize();
	IloNumArray d_sq(env,nCols);

	for (i = 0; i < nCols; i++) {
		d_sq[i] = pow(d[i], 2);
	}
	// Build model to generate the pack
	IloModel packModel(env);
	IloIntVarArray isInPack(env, nCols, 0, 1);
	IloNumVar temp(env,0,IloInfinity,ILOFLOAT); 
	packModel.add(IloMinimize(env,IloSum(xbar) - IloScalProd(xbar,isInPack)));
	packModel.add(b + 0.01 - IloScalProd(a,isInPack) == temp);
	packModel.add(temp*temp <= pow(omega,2) * IloScalProd(d_sq,isInPack));
	packModel.add(isInPack);

	IloCplex cplexPack(packModel);
	cplexPack.setOut(env.getNullStream());
	IloNumArray pack(env);
	cplexPack.solve();
	cplexPack.getValues(pack,isInPack);
	
	for (i = 0; i < nCols; i++) {
		pack[i] = IloRound(pack[i]);
	}

	IloNumArray toCheck = getComplement(pack);
	if (cplexPack.getObjValue() < 1 && !alreadyExists(toCheck, packs)) {
		IloNumArray2 toReturn(env,packs.getSize() + 1);
		for (i = 0; i < packs.getSize(); i++) {
			toReturn[i] = packs[i];
		}
		toReturn[i] = toCheck;
		return toReturn;
	}

	else {
		return packs;
	}

	cplexPack.end();
}

IloNumArray
	extendPack(IloNumArray	toExtend,
			   IloNumArray	a,
			   IloNumArray	d,
			   IloNum		omega) {

	int i, j;
	
	IloEnv env		= toExtend.getEnv();
	IloNum nCols	= a.getSize();
	IloNumArray d_sq(env,nCols);

	for (i = 0; i < nCols; i++) {
		d_sq[i] = pow(d[i], 2);
	}

	
	IloNumArray fromExtend	= getComplement(toExtend);
	IloIntArray	toIndices	= findIndices(toExtend);
	IloNumArray extendedPack(env, toExtend.getSize());
	
	for(i = 0; i < toExtend.getSize(); i++)
		extendedPack[i] = toExtend[i];

	IloIntArray fromIndices(env);
	IloNumArray minimumContributor(env,2);
	IloNum		fval, rho, remVal;
	bool canExtend;
	do {

		canExtend = true;
		fromIndices	= findIndices(fromExtend);
		IloNumArray tempArray(fromExtend);
		fval		= f(fromExtend, a, d_sq, omega);
		tempArray[fromIndices[0]] = 0;
		minimumContributor[0] = fromIndices[0];
		minimumContributor[1] =  fval - f(tempArray, a, d_sq, omega);
		tempArray[fromIndices[0]] = 1;
		for(i = 1; i < fromIndices.getSize(); i++) {
			tempArray[fromIndices[i]] = 0;
			rho = fval - f(tempArray, a, d_sq, omega);
			if(rho < minimumContributor[1]) {
				minimumContributor[0] = fromIndices[i];
				minimumContributor[1] = rho;
			}
			tempArray[fromIndices[i]] = 1;
		}

		tempArray[minimumContributor[0]] = 0;
		remVal	= f(tempArray, a, d_sq, omega);
		
		
		for(i = 0; i < toIndices.getSize(); i++) {
			tempArray[toIndices[i]] = 1;
			rho = f(tempArray, a, d_sq, omega) - remVal;
			if(minimumContributor[1] > rho) {
				canExtend = false;
				break;
			}
			tempArray[toIndices[i]] = 0;
		}

		if(canExtend){
			extendedPack[minimumContributor[0]] = 1;
			fromExtend[minimumContributor[0]] = 0;
		}
	}
	while(canExtend && IloSum(fromExtend) > 0);
	return extendedPack;
}

void
	buildCplexModel(IloModel			cplexModel,
					IloNumVarArray		cplexSolution,
					IloNumVarArray		temp,
					const IloNumArray2  a,
					const IloNumArray2  d,
					const IloNumArray	b, 
					const IloNum		omega,
					const IloNumArray	c,
					const IloInt		nRows,
					const IloInt		nCols) {

	int i, j;
	IloEnv env = cplexModel.getEnv();
	cplexSolution.clear();
	temp.clear();

	IloNumVarArray tmp1(env, nCols, 0, 1, ILOINT);
	IloNumVarArray tmp2(env, nRows, 0, IloInfinity, ILOFLOAT);
	cplexSolution.add(tmp1);
	temp.add(tmp2);
	tmp1.end();
	tmp2.end();

	cplexModel.add(IloMinimize(env, IloScalProd(c,cplexSolution)));
	cplexModel.add(cplexSolution);

	for (i = 0; i < nRows; i++) {
		IloExpr a_expr(env);
		IloExpr d_expr(env);
		for (j = 0; j < nCols; j++) {
			a_expr += cplexSolution[j] * a[i][j];
			d_expr += cplexSolution[j] * cplexSolution[j] * pow(d[i][j],2); 
		}
		cplexModel.add(b[i] - a_expr == temp[i]);
		cplexModel.add(pow(omega,2) * d_expr <= temp[i]*temp[i]);
		a_expr.end();
		d_expr.end();
	}
}

ILOUSERCUTCALLBACK3(CtCallback, 
					IloNumArray2,	coefficients, 
					IloNumVarArray, variables, 
					IloNumArray,	rhs) {
   IloInt n = rhs.getSize();
   for (IloInt i = 0; i < n; i++) {
      IloNum xrhs = rhs[i];
      if (xrhs < IloInfinity  &&  getValue(IloScalProd(coefficients[i],variables)) < xrhs) {
         IloRange cut;
         try {
            cut = (IloScalProd(coefficients[i],variables) >= xrhs);
            add(cut).end();
            rhs[i] = IloInfinity;
         }
         catch (...) {
            cut.end();
            throw;
         }
      }
   }
}

int
	main(int argc, char **argv)
{
	static IloEnv env;
	static IloNumArray2 a(env);
	static IloNumArray2 d(env);
	static IloNumArray b(env);
	static IloNum omega;
	static IloNumArray c(env);
	static ofstream fout_standard, fout_packs, fout_extendedPacks, fcout_packs, fcout_extendedPacks;
	int i;
	time_t start, end, start_p, end_p, start_exp, end_exp;

	try {
		  static IloNumArray relaxSol(env);
		  char input[100]			= "../Data/";
		  char s_output[100]			= "../StandardOutPutLogs/";
		  char p_output[100]			= "../PackOutPutLogs/";
		  char exp_output[100]		= "../ExtendedPackOutPutLogs/";
		  char packInequalities[100]	= "../PackInequalities/";
		  char exPackInequalities[100]	= "../ExtendedPackInequalities/";
		  char lp_files[100]			= "../LP-files/";
		  const char* input_file		= strcat(strcat(input,argv[1]),".dat");
		  const char* s_output_file		= strcat(strcat(s_output,argv[2]),".log");
		  const char* p_output_file		= strcat(strcat(p_output,argv[2]),".log");
		  const char* exp_output_file	= strcat(strcat(exp_output,argv[2]),".log");
		  const char* p_cuts_file		= strcat(strcat(packInequalities,argv[2]),".log");
		  const char* exp_cuts_file		= strcat(strcat(exPackInequalities,argv[2]),".log");
		  const char* lp_file		= strcat(strcat(lp_files,argv[2]),".lp");

		  const char* filename  = input_file;
		  ifstream file(filename);
		  if (!file) {
			 cerr << "ERROR: could not open file '" << filename
				  << "' for reading" << endl;
			 usage(argv[0]);
			 throw(-1);
		  }

		  fout_standard.open(s_output_file);
		  file >> omega >> c >> b >> a >> d;

		  IloInt nRows = b.getSize();
		  IloInt nCols = c.getSize();

		  if (a.getSize() != nRows ||
			  d.getSize() != nRows) {
				  cerr << "ERROR: Data file '" << filename << "' contains inconsistent data" << endl;
				  throw (-1);
		  }
		  
		  for (i = 0; i < nRows; i++) {
			  if (a[i].getSize() != nCols ||
				  d[i].getSize() != nCols) {
				  cerr << "ERROR: Data file '" << argv[0] << "' contains inconsistent data" << endl;
				  throw (-1);
			  }
		  }
		  
		  // Build CPLEX standard model

		  IloModel			cplexModel(env);
		  IloNumVarArray	temp(env);
		  IloNumVarArray	cplexSolution(env);
		  buildCplexModel(cplexModel, cplexSolution, temp, a, d, b, 
										omega, c, nRows, nCols);

		  // Solve CPLEX standard model

		  IloCplex cplexStandard(cplexModel);
		  cplexStandard.setOut(fout_standard);
		  IloNumArray cplexSolutionStandard(env);

		  cplexStandard.exportModel(lp_file);

		  time (&start);
		  cplexStandard.solve();
		  time (&end);
		  
		  cplexStandard.out() << endl << endl;
		  cplexStandard.out() << "Solution Status = " << cplexStandard.getStatus() << endl;
		  cplexStandard.getValues(cplexSolutionStandard,cplexSolution);
		  cplexStandard.out() << "Solution = " << findIndices(cplexSolutionStandard) << endl;
		  cplexStandard.out() << "Solution Objective Value = " << cplexStandard.getObjValue() << endl;
		  cplexStandard.out() << "The Time taken for optimizing the problem: " << difftime(end,start) << " seconds" << endl;
		  cplexStandard.out() << "The total Number of Branch and Bound Nodes Processed: " << cplexStandard.getNnodes() << endl << endl;

		  // Solving the linear relaxation of the Original Cplex Model
		  cplexStandard.clear();
		  IloConversion toContinous = IloConversion(env, cplexSolution, ILOFLOAT);
		  cplexModel.add(toContinous);
		  cplexStandard.extract(cplexModel);
		  IloNumArray solution(env);
		  cplexStandard.setOut(env.getNullStream());

		  time(&start);
		  cplexStandard.solve();
		  time(&end);

		  cplexStandard.out() << endl << endl;
		  cplexStandard.out() << "Solution Status = " << cplexStandard.getStatus() << endl;
		  cplexStandard.getValues(solution,cplexSolution);
		  cplexStandard.out() << "Solution = " << solution << endl;
		  cplexStandard.out() << "Solution Objective Value = " << cplexStandard.getObjValue() << endl;
		  cplexStandard.out() << "The Time taken for optimizing the problem: " << difftime(end,start) << " seconds" << endl;
		  
		  
		  // Finding the packs //

		  IloNumArray2	packs(env);
		  IloRangeArray	packIneq(env);
		  IloNumArray	rowIDs(env);
		  IloNumArray	packRhs(env);	
		  IloInt		packsOriginal, packsFinal = 0;
		  do {
			  packsOriginal = packsFinal;
			  for (i = 0; i < nRows; i++) {
				  packsFinal = packs.getSize();
				  packs = getPack(getRow(a,i), getRow(d,i), b[i], omega, solution, packs);
				  //cplexStandard.out() << endl << endl << packs << endl;
				  if (packsFinal < packs.getSize())
					  rowIDs.add(i);
			  }

			  packsFinal = packs.getSize();

			  for (i = packsOriginal; i < packsFinal; i++) {
				  packRhs.add(1);
				  packIneq.add(IloScalProd(packs[i],cplexSolution) >= 1);
			  }
		  
			  cplexModel.add(packIneq);
			  cplexStandard.clear();
			  cplexStandard.extract(cplexModel);
			  
			  time(&start);
			  cplexStandard.solve();
			  time(&end);
			  
			  cplexStandard.out() << endl << endl;
			  cplexStandard.out() << "Solution Status = " << cplexStandard.getStatus() << endl;
			  cplexStandard.getValues(solution,cplexSolution);
			  cplexStandard.out() << "Solution = " << solution << endl;
			  cplexStandard.out() << "Solution Objective Value = " << cplexStandard.getObjValue() << endl;
			  cplexStandard.out() << "The Time taken for optimizing the problem: " << difftime(end,start) << " seconds" << endl;
		  
		  } 
		  while(packsOriginal != packsFinal);
		  
		  fcout_packs.open(p_cuts_file);
		  fcout_packs << "Total Pack Inequalities Found : " << packsFinal << endl << endl;
		  for(i = 0; i < packsFinal; i++)
			  fcout_packs << packIneq[i] << endl << endl;

		  // Extending the packs //
		  
		  IloNumArray2	extendedPacks(env, packsFinal);
		  IloRangeArray extendedPackIneq(env);
		  IloNumArray extendedPackRhs(env, packsFinal);
		  for (i = 0; i < packsFinal; i++) {
			  extendedPacks[i] = extendPack(packs[i], getRow(a,rowIDs[i]), getRow(d,rowIDs[i]), omega);
			  extendedPackRhs[i] = IloSum(extendedPacks[i]) - IloSum(packs[i]) + 1;
			  extendedPackIneq.add(IloScalProd(extendedPacks[i],cplexSolution) >= extendedPackRhs[i]);
		  }

		  fcout_extendedPacks.open(exp_cuts_file);
		  fcout_extendedPacks << "Extended Pack Inequalities" << endl << endl;
		  for(i = 0; i < extendedPackIneq.getSize(); i++)
			  fcout_extendedPacks << extendedPackIneq[i] << endl << endl;


		  cplexStandard.clear();
		  cplexModel.remove(packIneq);
		  cplexModel.add(extendedPackIneq);
		  cplexStandard.extract(cplexModel);
		  
		  time(&start);
		  cplexStandard.solve();
		  time(&end);
		  
		  cplexStandard.out() << endl << endl;
		  cplexStandard.out() << "Solution Status = " << cplexStandard.getStatus() << endl;
		  cplexStandard.getValues(solution,cplexSolution);
		  cplexStandard.out() << "Solution = " << solution << endl;
		  cplexStandard.out() << "Solution Objective Value = " << cplexStandard.getObjValue() << endl;
		  cplexStandard.out() << "The Time taken for optimizing the problem: " << difftime(end,start) << " seconds" << endl;

		  // Reimposing Integer constraints
		  
		  cplexModel.remove(IloConversion(toContinous));		  
		  cplexModel.remove(extendedPackIneq);
		  
		  // Build CPLEX model with pack inequalities
		  
		  IloCplex cplexPacks(env);
		  cplexPacks.clear();
		  
		  cplexPacks.extract(cplexModel);

		  cplexPacks.use(CtCallback(env, packs, cplexSolution, packRhs));

		  fout_packs.open(p_output_file);
		  cplexPacks.setOut(fout_packs);
		  cplexPacks.setParam(IloCplex::Threads, 8);

		  time(&start_p);
		  cplexPacks.solve();
		  time(&end_p);
		  
		  cplexPacks.out() << endl << endl;
		  cplexPacks.out() << "Solution Status = " << cplexPacks.getStatus() << endl;
		  cplexPacks.getValues(solution,cplexSolution);
		  cplexPacks.out() << "Solution = " << findIndices(solution) << endl;
		  cplexPacks.out() << "Solution Objective Value = " << cplexPacks.getObjValue() << endl;
		  cplexPacks.out() << "The Time taken for optimizing the problem: " << difftime(end_p,start_p) << " seconds" << endl;
		  cplexPacks.out() << "The total Number of Branch and Bound Nodes Processed: " << cplexPacks.getNnodes() << endl << endl;

		  // Build CPLEX model with extended pack inequalities

		  IloModel	cplexExtendedPackModel(env);
		  cplexExtendedPackModel.add(cplexModel);
		  
		  IloCplex cplexExtendedPacks(cplexExtendedPackModel);
		  
		  cplexExtendedPacks.use(CtCallback(env, extendedPacks, cplexSolution, extendedPackRhs));

		  fout_extendedPacks.open(exp_output_file);
		  cplexExtendedPacks.setOut(fout_extendedPacks);
		  cplexExtendedPacks.setParam(IloCplex::Threads, 8);

		  time(&start_exp);
		  cplexExtendedPacks.solve();
		  time(&end_exp);

		  cplexExtendedPacks.out() << endl << endl;
		  cplexExtendedPacks.out() << "Solution Status = " << cplexExtendedPacks.getStatus() << endl;
		  cplexExtendedPacks.getValues(solution,cplexSolution);
		  cplexExtendedPacks.out() << "Solution = " << findIndices(solution) << endl;
		  cplexExtendedPacks.out() << "Solution Objective Value = " << cplexExtendedPacks.getObjValue() << endl;
		  cplexExtendedPacks.out() << "The Time taken for optimizing the problem: " << difftime(end_exp,start_exp) << " seconds" << endl;
		  cplexExtendedPacks.out() << "The total Number of Branch and Bound Nodes Processed: " << cplexExtendedPacks.getNnodes() << endl << endl;


		  cplexStandard.end(); cplexPacks.end(); cplexExtendedPacks.end();
	}
	catch (IloException& e) {
		cerr << "Concert exception caught: " << e << endl;
	}
	env.end();
	return 0;
}  // END main