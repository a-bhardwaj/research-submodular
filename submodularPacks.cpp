// -------------------------------------------------------------- -*- C++ -*-
// File: submodularPacks.cpp
// @author: Avinash Bhardwaj
// --------------------------------------------------------------------------
// Property of Berkeley Computational Optimization Group,
// University of California, Berkeley
// --------------------------------------------------------------------------
//
// submodularPacks.cpp -	Performance testing of the pack and extended pack
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


#define EPS		1e-4
#define bigM	1e4;

#include <ilcplex/ilocplex.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h> 
#include <math.h>

//@var		nCuts					:	To store the number of user cuts added.
//@var		rootRelaxationObjValue	:	To store the objective value of the root relaxation.

IloInt nCuts;
IloNum rootRelaxationObjValue; 

ILOSTLBEGIN

//@method	usage					:	To specify the usage error
static void 
	usage (const char *progname) {
		cerr << "Usage: " << progname << " <Output File> -c <CutsType> -a <AlgoType>" << endl;
		cerr << "      <Output File>          Output file to summarize the computation results. (Default: Same name as input file)" << endl;
		cerr << "      <CutsType>	          The type of cuts to use, 0: no cuts, 1: Packs, 2: Extended Packs. (Default: 0)" << endl;
		cerr << "      <AlgoType>	          The type of cover algorithm to use, 0: QCP Algorithm, 1: Sorting Algorithm. (Default: 0)" << endl << endl;
		cerr << " Exiting..." << endl;
} // END usage

//@method	findIndices				:	To find indices of the TRUE enteries of a binary array
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

//@method	f						:	To find the value of the function f := a*x + omega*norm(d*x)
IloNum 
	f(IloNumArray	x,
	  IloNumArray	a,
	  IloNumArray	d_sq,
	  IloNum		omega) {
	
	IloNum value = 0;
	value = IloScalProd(a,x) + omega*sqrt(IloScalProd(d_sq,x));
	return value;
}

//@method	getComplement			:	To find the complement of a binary array
IloNumArray
	getComplement(IloNumArray binaryArray) {
		IloEnv env = binaryArray.getEnv();
		IloNumArray binaryArrayComp(env, binaryArray.getSize());
		
		for (int i = 0; i < binaryArray.getSize(); i++)
			binaryArrayComp[i] = 1 - binaryArray[i];

		return binaryArrayComp;
}

//@method	alreadyExists			:	To identify if a row already exists in a matrix.
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


//@method	getRow					:	To retrive a rowId'th row of a matrix.
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

//@method	getPack					:	To retrive a pack for the conic quadratic constraint.
IloNumArray
	getPack(IloNumArray		a,
			IloNumArray		d,
			IloNum			b,
			IloNum			omega,
			IloNumArray		xbar) {

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
	packModel.add(b + EPS - IloScalProd(a,isInPack) == temp);
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
	
	return pack;

	cplexPack.end();
}

//@method	extendPack					:	To extend a pack inequality for the conic quadratic constraint.
IloNumArray
	extendPackIneq(IloNumArray	toExtend,
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

//@method	buildCplexModel				:	To build the CPLEX Model from given parameters.
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

ILOUSERCUTCALLBACK5(separatePackInequalities,
					IloNumVarArray,		cplexSolution,
					const IloNumArray2, a,
					const IloNumArray2, d,
					const IloNumArray,	b, 
					const IloNum,		omega) {
   if (getNnodes() == 0) {
	   try {
		   IloEnv env		=	getEnv();
		   IloInt cutAdded	=	0;
		   IloInt i			=	0;
		   IloInt nRows		=	b.getSize();
		   IloInt nCols		=	cplexSolution.getSize();

		   IloNumArray			X(env, nCols), newPack(env), packComplement(env);
		   IloNumArray2			packs(env);
		   
		   getValues(X,cplexSolution);


		   // get rootRelaxationObjValue first
		   IloInt numNodes = getNnodes();
		   if (numNodes == 0) {
			   rootRelaxationObjValue = getObjValue();
		   }

		   for (i = 0; i < nRows; i++) {
			   newPack = getPack(getRow(a,i), getRow(d,i), b[i], omega, X);
				  if(!alreadyExists(newPack, packs)) 
					  packs.add(newPack);
		   }

		   for (i = 0; i < packs.getSize(); i++) {
			   packComplement = getComplement(getRow(packs,i));
			   if(IloScalProd(X,packComplement) < 1) {
				   IloRange	cut;
				   try {
					   cut = (IloScalProd(packComplement,cplexSolution) >= 1);
					   add(cut).end();
					   nCuts++;
				   }
				   catch(...) {
					   cut.end();
					   throw;
				   }
			   }
		   }
	   }
	   catch (IloException &e) {
		   cerr << "Error in separatePackInequalities Callback: " << e << endl;
		   throw;
	   }
   }
}


ILOUSERCUTCALLBACK5(separateExtendedPackInequalities,
					IloNumVarArray,		cplexSolution,
					const IloNumArray2, a,
					const IloNumArray2, d,
					const IloNumArray,	b, 
					const IloNum,		omega) {
   if (getNnodes() == 0) {
	   try {
		   IloEnv env		=	getEnv();
		   IloInt cutAdded	=	0;
		   IloInt i			=	0;
		   IloInt nRows		=	b.getSize();
		   IloInt nCols		=	cplexSolution.getSize();

		   IloNumArray			X(env, nCols), newPack(env), packComplement(env), rowIds(env);
		   IloNumArray2			packs(env);
		   
		   getValues(X,cplexSolution);


		   // get rootRelaxationObjValue first
		   IloInt numNodes = getNnodes();
		   if (numNodes == 0) {
			   rootRelaxationObjValue = getObjValue();
		   }
		   
		   for (i = 0; i < nRows; i++) {
			   newPack = getPack(getRow(a,i), getRow(d,i), b[i], omega, X);
				  if(!alreadyExists(newPack, packs)) { 
					  packs.add(newPack);
					  rowIds.add(i);
				  }
		   }

		   IloNumArray	extended(env, nCols);
		   IloNum		rowId, rhs;
		   for (i = 0; i < packs.getSize(); i++) {
			   packComplement	= getComplement(getRow(packs,i));
			   rowId			= rowIds[i];
			   extended			= extendPackIneq(packComplement, getRow(a, rowId), getRow(d, rowId), omega);
			   rhs				= IloSum(extended) - IloSum(packComplement) + 1;
			   if(IloScalProd(X,packComplement) < 1) {
				   IloRange	cut;
				   try {
					   cut = (IloScalProd(extended, cplexSolution) >= rhs);
					   add(cut).end();
					   nCuts++;
				   }
				   catch(...) {
					   cut.end();
					   throw;
				   }
			   }
		   }
	   }
	   catch (IloException &e) {
		   cerr << "Error in separateExtendedPackInequalities Callback: " << e << endl;
		   throw;
	   }
   }
}


//callback to find rootRelaxationObjValue 
//when no cuts are added
ILOUSERCUTCALLBACK0(getRootRelaxationObjValue){
    IloInt numNodes = getNnodes();
    if (numNodes == 0){
        rootRelaxationObjValue = getObjValue();
    }
}

int
	main(int argc, char **argv)
{
	static IloEnv env;

	try {
		  static IloNumArray2 a(env);
		  static IloNumArray2 d(env);
		  static IloNumArray b(env);
		  static IloNum omega;
		  static IloNumArray c(env);
		  static FILE * fout;
		  int i, cutsType = 0, coverSeparationAlgo = 0;
		  time_t start, end;
		  double gap, cpuTime, objValue;
		  
		  char input[100]		= "../Data/";
		  char output[100]		= "../ComputationSummary/";
		  const char* input_file = strcat(strcat(input,argv[1]),".dat");
		  const char* output_file = strcat(strcat(output,argv[1]),".log");
		  
		  const char* filename  = input_file;

		  for (i = 2; i < argc-1; i++) { //command line options
			  if (!strncmp(argv[i],  "-c", 2) ) {
				  cutsType = atoi(argv[++i]); //The type of cuts to use, 0: no cuts, 1: Packs, 2: Extended Packs'
			  }

			  if (!strncmp(argv[i],  "-a", 2)) {
				  coverSeparationAlgo = atoi(argv[++i]); //The type of cover algorithm to use, 0: QCP Algorithm, 1: Sorting Algorithm 
			  }
		  }

		  ifstream file(filename);
		  if (!file) {
			 cerr << "ERROR: could not open file '" << filename
				  << "' for reading" << endl;
			 usage(argv[0]);
			 exit(1);
			 throw(-1);
		  }

		  fout = fopen(output_file, "w");
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
		  
		  // Build CPLEX model

		  IloModel			model(env);
		  IloNumVarArray	temp(env);
		  IloNumVarArray	variables(env);
		  buildCplexModel(model, variables, temp, a, d, b, 
										omega, c, nRows, nCols);

		  // Solve CPLEX standard model

		  IloCplex cplex(env);
		  cplex.setOut(env.getNullStream());
		  
		  
		  cplex.extract(model);
		  
		  // Setting the CPLEX Parameters

		  cplex.setParam(IloCplex::HeurFreq, -1);
		  cplex.setParam(IloCplex::MIQCPStrat, 1);
		  cplex.setParam(IloCplex::TiLim, 1800);
		  cplex.setParam(IloCplex::TreLim, 100);
		  cplex.setParam(IloCplex::MIPSearch, IloCplex::Traditional);
		  cplex.setParam(IloCplex::Threads, 1);
		  
		  /*
		  cplex.setParam(IloCplex::MIPInterval, 1000);
		  cplex.setParam(IloCplex::EpGap, 1e-09);
		  cplex.setParam(IloCplex::PolishAfterEpGap, 1e-09);
		  cplex.setParam(IloCplex::BarEpComp, 1e-12);
		  cplex.setParam(IloCplex::BarQCPEpComp, 1e-12);
		  cplex.setParam(IloCplex::MIPDisplay, 2);
		  cplex.setParam(IloCplex::MIPInterval, 1);
		  cplex.setParam(IloCplex::BarDisplay, 1);
		  cplex.setParam(IloCplex::FlowCovers, -1);
		  cplex.setParam(IloCplex::GUBCovers, -1);
		  cplex.setParam(IloCplex::FracCuts, -1);
		  cplex.setParam(IloCplex::FlowPaths, -1);
		  cplex.setParam(IloCplex::DisjCuts, -1);
		  cplex.setParam(IloCplex::Covers, -1);
		  cplex.setParam(IloCplex::Cliques, -1);
		  cplex.setParam(IloCplex::ImplBd, -1);
		  cplex.setParam(IloCplex::MCFCuts, -1);
		  cplex.setParam(IloCplex::MIRCuts, -1);
		  cplex.setParam(IloCplex::ZeroHalfCuts, -1);
		  cplex.setParam(IloCplex::EachCutLim, 0);
		  cplex.setParam(IloCplex::CutPass, -1);
		  cplex.setParam(IloCplex::TuningDisplay, 3);
		  cplex.setParam(IloCplex::MPSLongNum, 0);
		  */		  
		  
		  if (cutsType == 0) {
			  cplex.use(getRootRelaxationObjValue(env));
		  }
		  
		  if (cutsType == 1) {
			  cplex.use(separatePackInequalities(env,variables,a,d,b,omega));
		  }
			
		  if (cutsType == 2) {
			  cplex.use(separateExtendedPackInequalities(env,variables,a,d,b,omega));
		  }
		  
		  start		= clock();
		  cplex.solve();
		  end		= clock();
		  
		  objValue	= cplex.getObjValue();
		  gap		= 100*(objValue - rootRelaxationObjValue)/(objValue);
		  cpuTime	= (double)(end - start) / CLOCKS_PER_SEC;
		  if (cplex.getStatus() == IloAlgorithm::Optimal)
			  fprintf (fout,"Solution Status =  OPTIMAL \n");
		  else
			  fprintf (fout,"Solution Status =  NOT OPTIMAL \n");

		  fprintf (fout,"Objective Value =  %.3f \n", objValue);
		  fprintf (fout,"Number of Nodes =  %d \n", cplex.getNnodes());
		  fprintf (fout,"Number of User Cuts =  %d \n", nCuts);
		  fprintf (fout,"Root Relaxation Gap =  %.3f \n", gap);
		  fprintf (fout,"CPUTime =  %.3f \n", cpuTime);
		  
		  cplex.end();
		  fclose(fout);
	}
	catch (IloException& e) {
		cerr << "Concert exception caught: " << e << endl;
	}

	env.end();
	return 0;
}  // END main