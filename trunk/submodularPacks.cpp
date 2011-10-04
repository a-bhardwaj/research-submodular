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


#define EPS		1e-7
#define EPSI	1e-4

#include <ilcplex/ilocplex.h>
#include <stdlib.h>
#include <stdio.h>
#include <time.h> 
#include <math.h>

typedef IloArray<IloNumVarArray> NumVarMatrix;

//@var		rootRelaxationObjValue	:	To store the objective value of the root relaxation.

IloNum rootRelaxationObjValue; 

ILOSTLBEGIN


bool FileExists(const char *strFilename) {
	FILE* fp = fopen(strFilename, "r");
	bool exists = false;
	if (fp) {
		// file exists
		exists = true;
		fclose(fp);
	} 
	
	return exists;
}	
	
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
		IloIntArray indices(env);
		int i, l=0;
		for(i = 0; i < binaryArray.getSize(); i++){
			if(binaryArray[i]){
				indices.add(i);
				l++;
			}
		}
		return indices;
}

//@method	f						:	To find the value of the function f := a*x + omega*norm(d*x)
IloNum 
	f(IloNumArray	x,
	  IloNumArray	a,
	  IloNumArray	d,
	  IloNum		omega) {
	
	IloNum	nCols	= a.getSize();
	int i;

	IloNum value = 0, varValue = 0;
	for (i = 0; i < nCols; i++)
		varValue += x[i]*d[i]*d[i];

	value = IloScalProd(a,x) + omega*sqrt(varValue);
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


void 
	swap (int& x, 
		  int& y ) {
   int temp; 
   temp = x; 
   x = y; 
   y = temp; 
}

void 
	bubbleSort (IloNumArray Array, IloNumArray order) {
   IloInt size = Array.getSize();
   int last = size - 2; 
   int isChanged = 1;
   for(int i = 0; i < size; i++)
	   order[i] = i;
   while ( last >= 0 && isChanged) 
   { 
           isChanged = 0; 
           for ( int k = 0; k <= last; k++ ) 
			   if ( Array[k] > Array[k+1] ) 
               { 
				   swap ( Array[k], Array[k+1] );
                   swap ( order[k], order[k+1] );
				   isChanged = 1; 
               } 
           last--; 
   }
}


IloNumArray 
	getSubsets2(IloNumArray	Array, 
					  IloNumArray	order, 
					  IloNum		limit,
					  IloNumArray	a,
					  IloNumArray	d,
					  IloNum		b,
					  IloNum		omega) {
	IloEnv env = Array.getEnv();
	IloNum nCols = Array.getSize();
	int i;
	IloNumArray pack(env, nCols);
	bool packFound = false;

	for(i = 0; i < nCols; i++) {
		pack[i] = 1;
	}

	IloNum	sum = 0;
	i = 0;
	while(i < nCols) {
		if (a[order[i]] == 0) {
			i++;
			continue;
		}
		pack[order[i]] = 0;
		sum += Array[order[i]];
		if(f(pack,a,d,omega) > b + EPS) {
			packFound = true;
			break;
		}
		else {
			i++;
		}
	}	
	if(packFound) {
		return pack;
	}
	else
		return IloNumArray(env, nCols);
}

//@method	getPacksUsingSort		:	To retrive a pack for the conic quadratic constraint using Greedy Algorithm.
void
	getPackUsingSort2 (IloNumArray2	packs,
					  IloIntArray	rowIds,
					  IloInt		row,
					  IloNumArray	a,
					  IloNumArray	d,
					  IloNum		b,
					  IloNum		omega,
					  IloNumArray	xbar) {
	int i, j, k;
	IloEnv	env		= xbar.getEnv();
	IloNum	nCols	= xbar.getSize();

	IloNumArray arrayToSort(env, nCols), order(env, nCols);

	IloNumArray	newPack(env, nCols);
	IloNumArray c(env, nCols);
	for (i = 0; i < nCols; i++) {
		c[i] = pow(omega*d[i],2);
	}
	IloNum	lambda, mu;	
	for (i = 0; i < nCols; i++) {
		if(a[i] == 0)
				continue;
		for (j = i + 1; j < nCols; j++) {
			if(a[j] == 0)
				continue;
			lambda	= (c[j]*xbar[i] - c[i]*xbar[j])/(c[j]*a[i] - c[i]*a[j]);
			mu		= (a[j]*xbar[i] - a[i]*xbar[j])/(c[i]*a[j] - c[j]*a[i]);
			//if(lambda <= -EPS && mu <= -EPS) {
				for (k = 0; k < nCols; k++) {
					arrayToSort[k] = xbar[k]/(lambda*a[k] + mu*c[k] + pow(EPS,2));
				}
				bubbleSort(arrayToSort, order);
				newPack = getSubsets2(xbar, order, 1, a, d, b, omega);
				if(IloSum(newPack) > 0 && !alreadyExists(newPack, packs)) {
					packs.add(newPack);
					rowIds.add(row);
				}
			//}
		}
	}
}


IloNumArray 
	getSubsets(IloNumArray	Array, 
			   IloNumArray	order, 
			   IloNum		limit,
			   IloNumArray	a,
			   IloNumArray	d,
			   IloNum		b,
			   IloNum		omega) {
	IloEnv env = Array.getEnv();
	IloNum nCols = Array.getSize();
	int i;
	IloNumArray pack(env, nCols);
	bool packFound = false;

	for(i = 0; i < nCols; i++) {
		pack[i] = 1;
	}

	IloNum	sum = 0;
	i = 0;
	while(i < nCols) {
		if (a[order[i]] == 0) {
			i++;
			continue;
		}
		sum += Array[i];
		if(sum < limit - EPS) {
			pack[order[i]] = 0;
			if (f(pack,a,d,omega) > b + EPS) {
				packFound = true;
				break;
			}
			i++;
		}
		else {
			break;
		}
	}	
	if(packFound) {
		//env.out() << "The Pack I am returning is : " << pack << " and also the flag value for it is : " << packFound << endl;
		return pack;
	}
	else
		return IloNumArray(env,nCols);
}

//@method	getPacksUsingSort		:	To retrive a pack for the conic quadratic constraint using Greedy Algorithm.
IloNumArray
	getPackUsingSort(IloNumArray	a,
					  IloNumArray	d,
					  IloNum		b,
					  IloNum		omega,
					  IloNumArray	xbar) {
	int i;
	IloEnv		env			= xbar.getEnv();
	IloNum		nCols		= xbar.getSize();

	IloNumArray arrayToSort(env, nCols);
	for (i = 0; i < nCols; i++)
		arrayToSort[i] = xbar[i];

	// Sort and get the sorted order
	IloNumArray order(env, nCols);
	bubbleSort(arrayToSort,order);
	//env.out() << "Array \t\t order \t a \t\t d\t " << b << endl << endl; 
	for (i = 0; i < nCols; i++) {
	/*env.out() << arrayToSort[i] << "\t\t"<< order[i]
								<< "\t"<< a[order[i]]
								<< "\t\t"<< d[order[i]] << endl;*/ 
	}
	return getSubsets(arrayToSort, order, 1, a, d, b, omega);
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
	packModel.add(b + EPS - IloScalProd(a,isInPack) <= temp);
	packModel.add(temp*temp <= pow(omega,2) * IloScalProd(d_sq,isInPack));
	packModel.add(isInPack);

	IloCplex cplexPack(packModel);
	cplexPack.setOut(env.getNullStream());
	IloNumArray pack(env, nCols);
	cplexPack.solve();
	
	if (cplexPack.getStatus() == IloAlgorithm::Optimal) {
		cplexPack.getValues(pack,isInPack);
		for (i = 0; i < nCols; i++) {
			pack[i] = IloRound(pack[i]);
		}
	}
	
	return pack;

	cplexPack.end();
}

//@method	makeMaximal					:	To make the pack maximal.
void
	makeMaximal(IloNumArray toExtend,
				IloNumArray	a,
				IloNumArray	d,
				IloNum		omega,
				IloNum		b) {
	int i;

	IloNum nCols	= a.getSize();
	IloNumArray fromExtend	= getComplement(toExtend);
	
	IloIntArray fromIndices = findIndices(fromExtend);
	
	for(i = 0; i < fromIndices.getSize(); i++) {
		if (a[fromIndices[i]] == 0) {
			toExtend[fromIndices[i]] = 1;
			continue;
		}
		toExtend[fromIndices[i]] = 1;
		if(f(toExtend, a , d, omega) <= b) {
			toExtend[fromIndices[i]] = 0;
		}
	}
}

IloNum 
	computeRho(IloNumArray	BinaryArray,
			   IloNum		indexplus,
			   IloNum		indexminus,
			   IloNumArray	a,
			   IloNumArray	d,
			   IloNum		omega) {
	int i, nCols = BinaryArray.getSize();
	IloEnv env = BinaryArray.getEnv();
	IloNumArray Array(env, nCols);

	for(i = 0; i < nCols; i++) {
		Array[i] = BinaryArray[i];
	}
	Array[indexminus] = 0;
	IloNum fval = f(Array, a, d, omega), fvalNew;
	Array[indexplus] = 1;
	fvalNew = f(Array, a, d, omega);
	IloNum rho = fvalNew - fval;

	return rho;
}

//@method	extendPack					:	To extend a pack inequality for the conic quadratic constraint.
IloNumArray
	extendPackIneq(IloNumArray	toExtend,
				   IloNumArray	a,
				   IloNumArray	d,
				   IloNum		omega,
				   IloNum		b) {

	int i, j, fromIndex;
	
	IloEnv env		= toExtend.getEnv();
	IloNum nCols	= a.getSize();

	IloNumArray fromExtend	= getComplement(toExtend);
	for (i = 0; i < nCols; i++) {
		if (a[i] == 0)
			fromExtend[i] = 0;
	}

	IloNum delta = f(fromExtend,a,d,omega) - b;

	IloIntArray	toIndices	= findIndices(toExtend);
	IloNumArray extendedPack(env, toExtend.getSize());
	
	for(i = 0; i < nCols; i++)
		extendedPack[i] = toExtend[i];

	IloIntArray fromIndices = findIndices(fromExtend);
	IloNum toSize = toIndices.getSize(), fromSize = fromIndices.getSize();
	IloNumArray toRhos(env, toSize);
	IloNum fromMin, toMin;

	for(i = 0; fromSize > 0 ; i++) {
		IloNumArray fromRhos(env,fromSize);

		for(i = 0; i < fromSize; i++) 
			fromRhos[i] = computeRho(fromExtend, fromIndices[i], fromIndices[i], a, d, omega);
		
		fromMin = IloMin(fromRhos);

		for(i = 0; i < fromSize; i++) {
			if(fromRhos[i] == fromMin) {
				fromIndex = i;
				break;
			}
		}
		
		for(i = 0; i < toSize; i++)
			toRhos[i] = computeRho(fromExtend, toIndices[i], fromIndices[fromIndex], a, d, omega);

		toMin = IloMin(toRhos);

		if (fromMin < toMin + delta) {
			extendedPack[fromIndices[fromIndex]] = 1;
			fromExtend[fromIndices[fromIndex]] = 0;
			fromIndices = findIndices(fromExtend);
			fromSize = fromIndices.getSize();
			delta = delta - IloMax(fromMin - toMin, 0);
		}
		else
			break;

		fromRhos.end();
		}
	return extendedPack;
}

IloNum findLiftCoeff(IloNumArray packcomp,
					 IloNumArray J,
					 IloNumArray pack,
					 IloNumArray packIndices,
					 IloNumArray coeffs,
					 IloNumArray a,
					 IloNumArray d,
					 IloNum omega,
					 IloNum b,
					 int k){
	IloNum coeff;
	int j,l;
	pack[k] = 0;
	l = 0;
	IloEnv env = a.getEnv();
	int nCols = a.getSize();
	IloNumVar tempvar(env, 0, IloInfinity);
	IloIntVarArray x(env, nCols, 0, 1);
	IloModel liftmodel(env);
	IloCplex liftCplex(env);
	liftmodel.add(x);
	IloConstraint cons1, cons2;
	IloExpr mean(env), var(env), obj(env);
	obj = IloScalProd(packcomp,x);
	for(j = 0; j < nCols; j++) {
		if(J[j]) {
			obj += -coeffs[j]*(1-x[j]);
		}
		if(pack[j]) {
			mean += a[j];
			var += d[j]*d[j];
		}

		if(packcomp[j] || J[j]) {
			mean += a[j]*x[j];
			var += d[j]*d[j]*x[j]*x[j];
		}
	}

	liftmodel.add(IloMinimize(env,obj));
	cons1 = (tempvar <= b - mean);
	cons2 = (tempvar*tempvar >= omega*omega*var);

	liftmodel.add(cons1);
	liftmodel.add(cons2);
	liftCplex.extract(liftmodel);
	liftCplex.setOut(env.getNullStream());
	liftCplex.solve();

	coeff = liftCplex.getObjValue() - 1;
	IloNumArray vals(env);
	liftCplex.getValues(vals,x);
	x.endElements(); x.end(); liftmodel.end(); liftCplex.end(); cons1.end(); cons2.end();
	mean.end(); var.end(); obj.end(); vals.end();
	return coeff;
}


IloNumArray
	liftPackIneq(IloNumArray packcomp, 
				 IloNumArray a, 
				 IloNumArray d, 
				 IloNum		omega, 
				 IloNum		b) {
	int i, j, k, l;
	IloEnv env		= packcomp.getEnv();
	IloNum nCols	= a.getSize();
	IloNumArray packIndices(env);
	IloNumArray pack(env,nCols);
	IloNumArray J(env,nCols);
	IloNumArray coeffs(env,nCols);
	
	for(i = 0; i < nCols; i++) {
		J[i] = 0;
		coeffs[i] = 0;
		if(a[i] && !packcomp[i]) {
			packIndices.add(i);
			pack[i] = 1;
		}
		else
			pack[i] = 0;
	}
	for(i = 0; i < packIndices.getSize(); i++) {
		k = packIndices[i];
		coeffs[k] = findLiftCoeff(packcomp,J,pack,packIndices,coeffs,a,d,omega,b,k);
			J[k] = 1;
	}
	return coeffs;
}
void
	buildCplexModel2(IloModel			cplexModel,
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
	
	NumVarMatrix cz(env, nRows);
	
	/* The objective function should be minimization with positive coefficients 
	   or maximization with negative coefficients otherwise the trivial solution
	   is all variables set to 1
	*/
	
	cplexModel.add(IloMinimize(env, IloScalProd(c,cplexSolution)));
	
	cplexModel.add(cplexSolution);

	for (i = 0; i < nRows; i++) {
		IloExpr a_expr(env);
		IloExpr d_expr(env);
		IloNumVarArray tempcz(env,nCols,-IloInfinity, IloInfinity);
		cz[i] = tempcz;
		for (j = 0; j < nCols; j++) {
			a_expr += cplexSolution[j] * a[i][j];
			cplexModel.add(cz[i][j] - omega*d[i][j]*cplexSolution[j] == 0);
			d_expr += cz[i][j]*cz[i][j] ; 
		}
		cplexModel.add(b[i] - a_expr >= temp[i]);
		cplexModel.add(d_expr <= temp[i]*temp[i]);
		a_expr.end();
		d_expr.end();
	}
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

	/* The objective function should be minimization with positive coefficients 
	   or maximization with negative coefficients otherwise the trivial solution
	   is all variables set to 1
	*/
	
	cplexModel.add(IloMinimize(env, IloScalProd(c,cplexSolution)));
	
	cplexModel.add(cplexSolution);

	for (i = 0; i < nRows; i++) {
		IloExpr a_expr(env);
		IloExpr d_expr(env);
		for (j = 0; j < nCols; j++) {
			a_expr += cplexSolution[j] * a[i][j];
			d_expr += cplexSolution[j] * cplexSolution[j] * pow(d[i][j],2); 
		}
		cplexModel.add(b[i] - a_expr >= temp[i]);
		cplexModel.add(pow(omega,2) * d_expr <= temp[i]*temp[i]);
		a_expr.end();
		d_expr.end();
	}
}

ILOUSERCUTCALLBACK7(separatePackInequalities,
					IloNumVarArray,		cplexSolution,
					const IloNumArray2, a,
					const IloNumArray2, d,
					const IloNumArray,	b, 
					const IloNum,		omega,
					const IloInt,		coverAlgo,
					const IloInt,		useMaximal) {
   if (getNnodes() == 0) {
	   try {
		   IloEnv env		=	getEnv();
		   IloInt cutAdded	=	0;
		   IloInt nRows		=	b.getSize();
		   IloInt nCols		=	cplexSolution.getSize();

		   IloNumArray			X(env, nCols), newPack(env, nCols), packComplement(env, nCols), currentPack(env, nCols);
		   IloIntArray			rowIds(env);
		   IloNumArray2			packs(env);
		   
		   int i, j, rowId;

		   getValues(X,cplexSolution);



		   // get rootRelaxationObjValue first
		   IloInt numNodes = getNnodes();
		   if (numNodes == 0) {
			   rootRelaxationObjValue = getObjValue();
		   }
		   if(coverAlgo == 1) {
			   for (i = 0; i < nRows; i++) {
				   newPack = getPackUsingSort(a[i], d[i], b[i], omega, X);
				   if(IloSum(newPack) > 0 && !alreadyExists(newPack, packs)) {
						  packs.add(newPack);
						  rowIds.add(i);
					  }
			   }

			   for (i = 0; i < packs.getSize(); i++) {
				   rowId = rowIds[i];
				   currentPack = packs[i];
				   if(useMaximal)
					   makeMaximal(currentPack, a[rowId], d[rowId], omega, b[rowId]);
				   packComplement = getComplement(currentPack);
				   
				   IloRange	cut;
				   try {
					   cut = (IloScalProd(packComplement,cplexSolution) >= 1);
					   add(cut).end();
				   }
				   
				   catch(...) {
					   cut.end();
					   throw;
				   }
			   }
		   }

		   else if(coverAlgo == 2) {
			   for (i = 0; i < nRows; i++) {
				   getPackUsingSort2(packs ,rowIds, i, a[i], d[i], b[i], omega, X);
			   }

			   for (i = 0; i < packs.getSize(); i++) {
				   rowId = rowIds[i];
				   currentPack = packs[i];
				   if(useMaximal)
					   makeMaximal(currentPack, a[rowId], d[rowId], omega, b[rowId]);
				   packComplement = getComplement(currentPack);
				   
				   if(IloScalProd(packComplement,X) < 1 - EPSI) {
					   IloRange	cut;
					   try {
						   cut = (IloScalProd(packComplement,cplexSolution) >= 1);
						   add(cut).end();
					   }
				   
					   catch(...) {
						   cut.end();
						   throw;
					   }
				   }
			   }
		   }

		   else {
			   for (i = 0; i < nRows; i++) {
				   newPack = getPack(a[i], d[i], b[i], omega, X);
				   if(IloSum(newPack) > 0 && !alreadyExists(newPack, packs)) {
						  packs.add(newPack);
						  rowIds.add(i);
				   }
			   }

			   for (i = 0; i < packs.getSize(); i++) {
				   rowId = rowIds[i];
				   currentPack = packs[i];
				   if(useMaximal)
					   makeMaximal(currentPack, a[rowId], d[rowId], omega, b[rowId]);
				   
				   packComplement = getComplement(currentPack);
				   if(IloScalProd(X,packComplement) < 1 - EPS) {
					   IloRange	cut;
					   try {
						   cut = (IloScalProd(packComplement,cplexSolution) >= 1);
						   add(cut).end();
					   }
					   catch(...) {
						   cut.end();
						   throw;
					   }
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


ILOUSERCUTCALLBACK7(separateExtendedPackInequalities,
					IloNumVarArray,		cplexSolution,
					const IloNumArray2, a,
					const IloNumArray2, d,
					const IloNumArray,	b, 
					const IloNum,		omega,
					const IloInt,		coverAlgo,
					const IloInt,		useMaximal) {
   if (getNnodes() == 0) {
	   try {
		   IloEnv env		=	getEnv();
		   IloInt cutAdded	=	0;
		   IloInt nRows		=	b.getSize();
		   IloInt nCols		=	cplexSolution.getSize();

		   IloNumArray	X(env, nCols), extended(env, nCols), packComplement(env, nCols), newPack(env, nCols), currentPack(env,nCols);
		   IloIntArray	rowIds(env);
		   IloNumArray2	packs(env);
		   IloNumArray currentA(env, nCols), currentD(env, nCols);

		   int i, j, rhs, rowId;
		   getValues(X,cplexSolution);


		   // get rootRelaxationObjValue first
		   IloInt numNodes = getNnodes();
		   if (numNodes == 0) {
			   rootRelaxationObjValue = getObjValue();
		   }
		   if(coverAlgo == 1) {
			   for (i = 0; i < nRows; i++) {
				   newPack = getPackUsingSort(a[i], d[i], b[i], omega, X);
				   if(IloSum(newPack) > 0 && !alreadyExists(newPack, packs)) {
						  packs.add(newPack);
						  rowIds.add(i);
					  }
			   }
			   
			   for (i = 0; i < packs.getSize(); i++) {
				   rowId = rowIds[i];
				   currentPack		= packs[i];
				   currentA			= a[rowId];
				   currentD			= d[rowId];
				   if(useMaximal)
					   makeMaximal(currentPack, currentA, currentD, omega, b[rowId]);
				   packComplement	= getComplement(currentPack);
				   rhs				= IloSum(packComplement);
				   extended			= extendPackIneq(packComplement, currentA, currentD, omega, b[rowId]);
				   rhs				= IloSum(extended) - rhs + 1;
				   
				   IloRange	cut;
				   try {
					   cut = (IloScalProd(extended,cplexSolution) >= rhs);
					   add(cut).end();
				   }
				   
				   catch(...) {
					   cut.end();
					   throw;
				   }
			   }
		   }

		   else if (coverAlgo == 2) {			   
			   for (i = 0; i < nRows; i++) {
				   getPackUsingSort2(packs ,rowIds, i, a[i], d[i], b[i], omega, X);
			   }

			   for (i = 0; i < packs.getSize(); i++) {
				   rowId = rowIds[i];
				   currentPack		= packs[i];
				   currentA			= a[rowId];
				   currentD			= d[rowId];
				   if(useMaximal)
					   makeMaximal(currentPack, currentA, currentD, omega, b[rowId]);
				   packComplement	= getComplement(currentPack);
				   rhs				= IloSum(packComplement);
				   extended			= extendPackIneq(packComplement, currentA, currentD, omega, b[rowId]);
				   rhs				= IloSum(extended) - rhs + 1;
				   
				   if(IloScalProd(extended,X) < rhs - EPSI) {
					   IloRange	cut;
					   try {
						   cut = (IloScalProd(extended,cplexSolution) >= rhs);
						   add(cut).end();
					   }
				   
					   catch(...) {
						   cut.end();
						   throw;
					   }
				   }
			   }
		   }

		   else {
			   for (i = 0; i < nRows; i++) {
				   newPack = getPack(a[i], d[i], b[i], omega, X);
				   if(IloSum(newPack) > 0 && !alreadyExists(newPack, packs)) { 
						  packs.add(newPack);
						  rowIds.add(i);
					  }
			   }

			   IloNum		rowId;
			   for (i = 0; i < packs.getSize(); i++) {
				   rowId = rowIds[i];
				   currentPack		= packs[i];
				   //env.out() << "The Original Pack Inequality is .. " << (IloScalProd(getComplement(currentPack),cplexSolution) >= 1)  << endl;
				   currentA			= a[rowId];
				   currentD			= d[rowId];
				   if(useMaximal)
					   makeMaximal(currentPack, currentA, currentD, omega, b[rowId]);
				   packComplement	= getComplement(currentPack);
				   //env.out() << "The Maximal Pack Inequality is .. " << (IloScalProd(packComplement,cplexSolution) >= 1)  << endl;
				   rhs				= IloSum(packComplement);
				   extended			= extendPackIneq(packComplement, currentA, currentD, omega, b[rowId]);
				   rhs				= IloSum(extended) - rhs + 1;
				   if(IloScalProd(X,packComplement) < 1 - EPS) {
					   IloRange	cut;
					   try {
						   cut = (IloScalProd(extended, cplexSolution) >= rhs);
						   add(cut).end();
					   }
					   catch(...) {
						   cut.end();
						   throw;
					   }
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

ILOUSERCUTCALLBACK5(separateLiftedPackInequalities,
					IloNumVarArray,		cplexSolution,
					const IloNumArray2, a,
					const IloNumArray2, d,
					const IloNumArray,	b, 
					const IloNum,		omega) {
   if (getNnodes() == 0) {
	   try {
		   IloEnv env		=	getEnv();
		   IloInt cutAdded	=	0;
		   IloInt nRows		=	b.getSize();
		   IloInt nCols		=	cplexSolution.getSize();

		   IloNumArray	X(env, nCols), extended(env, nCols), packComplement(env, nCols), currentPack(env,nCols);
		   IloNumArray  coeffs(env,nCols);
		   IloIntArray	rowIds(env);
		   IloNumArray2	packs(env);
		   IloNumArray currentA(env, nCols), currentD(env, nCols);

		   int i, j, rhs, rowId;
		   getValues(X,cplexSolution);

		   IloInt numNodes = getNnodes();
			if (numNodes == 0){
				rootRelaxationObjValue = getBestObjValue();
			}

		   for (i = 0; i < nRows; i++) {
				   getPackUsingSort2(packs ,rowIds, i, a[i], d[i], b[i], omega, X);
			}

			for (i = 0; i < packs.getSize(); i++) {
				rowId = rowIds[i];
				currentPack		= packs[i];
				currentA			= a[rowId];
				currentD			= d[rowId];
				makeMaximal(currentPack, currentA, currentD, omega, b[rowId]);
				packComplement	= getComplement(currentPack);
				coeffs			= liftPackIneq(packComplement,currentA,currentD,omega,b[rowId]);
				rhs	= IloSum(coeffs) + 1;
				if(IloScalProd(packComplement,X) + IloScalProd(coeffs,X) < rhs - EPSI) {
					IloRange	cut;
					try {
					   cut = (IloScalProd(packComplement,cplexSolution) + IloScalProd(coeffs,cplexSolution) >= rhs);
					   add(cut).end();
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
ILOMIPINFOCALLBACK0(getRootRelaxationObjValue){
    IloInt numNodes = getNnodes();
    if (numNodes == 0){
        rootRelaxationObjValue = getBestObjValue();
    }
}

ILOLAZYCONSTRAINTCALLBACK0(getRootRelaxationObjValueLazy){
    IloInt numNodes = getNnodes();
    if (numNodes == 0){
        rootRelaxationObjValue = getBestObjValue();
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
		  static ofstream fout;
		  int i, cutsType = 2, coverSeparationAlgo = 2, useMaximal = 1, useLifted = 1;
		  time_t start, end;
		  double gap, cpuTime, objValue;
		  
		  char input[100]	= "../Data/";
		  char output[100]	= "../ComputationSummary/";
		  const char* input_file = strcat(strcat(input,argv[1]),".dat");
		  
		  const char* filename  = input_file;

		  for (i = 2; i < argc-1; i++) { //command line options
			  if (!strncmp(argv[i],  "-c", 2) ) {
				  cutsType = atoi(argv[++i]); //The type of cuts to use, 0: no cuts, 1: Packs, 2: Extended Packs'
			  }

			  if (!strncmp(argv[i],  "-a", 2)) {
				  coverSeparationAlgo = atoi(argv[++i]); //The type of cover algorithm to use, 0: QCP Algorithm, 1: Sorting Algorithm 
			  }

			  if (!strncmp(argv[i],  "-m", 2)) {
				  useMaximal = atoi(argv[++i]); //Whether to use maximal packs for QCP algorithm 
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


		  // Change between buildCplexModel() and buildCplexModel2();

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
		  
		  cplex.setParam(IloCplex::PreInd,0);
		  cplex.setParam(IloCplex::RelaxPreInd,0);
		  cplex.setParam(IloCplex::PreslvNd,-1);
		  cplex.setParam(IloCplex::Reduce,0);

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
		  /*cplex.setParam(IloCplex::CutPass, -1);
		  cplex.setParam(IloCplex::TuningDisplay, 3);
		  cplex.setParam(IloCplex::MPSLongNum, 0);
		  */		  
		  
		  if (cutsType == 0) {
			  cplex.use(getRootRelaxationObjValue(env));
			  cplex.use(getRootRelaxationObjValueLazy(env));
		  }
		  
		  if (cutsType == 1) {
			  cplex.use(separatePackInequalities(env,variables,a,d,b,omega,coverSeparationAlgo,useMaximal));
			  cplex.use(getRootRelaxationObjValueLazy(env));
		  }
			
		  if (cutsType == 2) {
			  if(useLifted) {
				  cplex.use(separateLiftedPackInequalities(env,variables,a,d,b,omega));
				  cplex.use(getRootRelaxationObjValueLazy(env));
			  }
			  else {
				  cplex.use(separateExtendedPackInequalities(env,variables,a,d,b,omega,coverSeparationAlgo,useMaximal));
				  cplex.use(getRootRelaxationObjValueLazy(env));
			  }
		  }
		  
		  start		= clock();
		  cplex.solve();
		  end		= clock();
		  
		  objValue	= cplex.getObjValue();
		  gap		= fabs(100*(objValue - rootRelaxationObjValue)/(objValue));
		  cpuTime	= (double)(end - start) / CLOCKS_PER_SEC;
		  
		  const char* output_file;

		  if (cutsType == 0 && coverSeparationAlgo == 0 && useMaximal == 0) 
			  output_file = strcat(strcat(output,"NoPacks"),".log");
		  else if (cutsType == 1 && coverSeparationAlgo == 0 && useMaximal == 0) 
			  output_file = strcat(strcat(output,"PacksQCP"),".log");
		  else if (cutsType == 1 && coverSeparationAlgo == 0 && useMaximal == 1) 
			  output_file = strcat(strcat(output,"PacksQCPMaximal"),".log");
		  else if (cutsType == 1 && coverSeparationAlgo == 1 && useMaximal == 0) 
			  output_file = strcat(strcat(output,"PacksGreedy"),".log");
		  else if (cutsType == 1 && coverSeparationAlgo == 1 && useMaximal == 1) 
			  output_file = strcat(strcat(output,"PacksGreedyMaximal"),".log");
		  else if (cutsType == 1 && coverSeparationAlgo == 2 && useMaximal == 0) 
			  output_file = strcat(strcat(output,"PacksDual"),".log");
		  else if (cutsType == 1 && coverSeparationAlgo == 2 && useMaximal == 1) 
			  output_file = strcat(strcat(output,"PacksDualMaximal"),".log");
		  else if (cutsType == 2 && coverSeparationAlgo == 0 && useMaximal == 0) 
			  output_file = strcat(strcat(output,"ExtendedPacksQCP"),".log");
		  else if (cutsType == 2 && coverSeparationAlgo == 0 && useMaximal == 1) 
			  output_file = strcat(strcat(output,"ExtendedPacksQCPMaximal"),".log");
		  else if (cutsType == 2 && coverSeparationAlgo == 1 && useMaximal == 0) 
			  output_file = strcat(strcat(output,"ExtendedPacksGreedy"),".log");
		  else if (cutsType == 2 && coverSeparationAlgo == 1 && useMaximal == 1) 
			  output_file = strcat(strcat(output,"ExtendedPacksGreedyMaximal"),".log");
		  else if (cutsType == 2 && coverSeparationAlgo == 2 && useMaximal == 0) 
			  output_file = strcat(strcat(output,"ExtendedPacksDual"),".log");
		  else if (cutsType == 2 && coverSeparationAlgo == 2 && useMaximal == 1) 
			  output_file = strcat(strcat(output,"ExtendedPacksDualMaximal"),".log");

		  if(FileExists(output_file)) {
			  fout.open(output_file, ios::app);
			  fout << nRows << "\t";
			  fout << nCols << "\t";
			  fout << omega << "\t";
			  if (cplex.getStatus() == IloAlgorithm::Optimal)
				  fout << "OPTIMAL \t" ;
			  else
				  fout << "NOT OPTIMAL \t";

			  fout << objValue << "\t";
			  fout << cplex.getNcuts(IloCplex::CutUser) << "\t";
			  fout << gap << "\t" ;
			  fout << cplex.getNnodes() << "\t" ;
			  fout << cpuTime << "\n";
		  }

		  else {
			  fout.open(output_file);
			  fout << "CONSTRA\t";
			  fout << "VARIABL\t";
			  fout << "OMEGA  \t";
			  fout << "STATUS \t";
			  fout << "OBJ VAL\t";
			  fout << "# CUTS \t";
			  fout << "GAP VAL\t";
			  fout << "# NODES\t";
			  fout << "CPUTIME\n";
			  fout << nRows << "\t";
			  fout << nCols << "\t";
			  fout << omega << "\t";
			  if (cplex.getStatus() == IloAlgorithm::Optimal)
				  fout << "OPTIMAL \t" ;
			  else
				  fout << "NOT OPTIMAL \t";

			  fout << objValue << "\t";
			  fout << cplex.getNcuts(IloCplex::CutUser) << "\t";
			  fout << gap << "\t" ;
			  fout << cplex.getNnodes() << "\t" ;
			  fout << cpuTime << "\n";
		  }
		  cplex.end();
		  fout.close();
	}
	catch (IloException& e) {
		cerr << "Concert exception caught: " << e << endl;
	}

	env.end();
	return 0;
}  // END main