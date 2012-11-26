package web;
import java.util.*;
import java.io.*;


public class DPLLsolver{

  private static Interpretation satisfiable (Conjunction problem){
    // Takes a conjunction and returns null if it is not satisfiable,
    // or the mappings if it is.

    Conjunction problemclone = (Conjunction)problem.clone(); // Prevent munging, in case
    List clauses = problemclone.getClauses();
    Set symbols = problemclone.getVariables();
    Interpretation model = new Interpretation();
    
    return DPLL(clauses, symbols, model);
    
  }

  private static Interpretation DPLL(List clauses, Set symbols, Interpretation model){
    // clauses is a list of disjunctions
    // symbols is a list of variables
    // model contains variable-value mapping

    // check to see if all clauses are true with model; if so, return model;
    // check to see if any clause is false with model; if so, return null;
    System.out.println("DPLL testing clauses " + clauses.toString() + " symbols " + symbols.toString() + " with model " + model.toString());
    boolean isTrue = true;
    boolean isFalse = false;
    Iterator clauseiterator = clauses.iterator();
    while (clauseiterator.hasNext()){
      Disjunction thisclause = (Disjunction) clauseiterator.next();
      Boolean satisfied = thisclause.isSatisfied(model);
      if (satisfied != Boolean.TRUE)
	isTrue = false;
      if (satisfied == Boolean.FALSE)
	isFalse = true;
    }
    if (isFalse)
      {
	return null;}
    if (isTrue)
      {
      return model;}
    
    // else, check for pure symbol and map it;
    Vector pmapping = getPureSymbol(symbols, clauses, model);
    if (pmapping != null){
      Variable p = (Variable) pmapping.elementAt(0);
      Boolean pvalue = (Boolean) pmapping.elementAt(1);
      model.put(p, pvalue);
      symbols.remove(p);
        System.out.println("Pure symbol " + p.toString() + " assigned " + pvalue.toString());
      return DPLL(clauses, symbols, model); 
    }
    // if that doesn't work, check for a unit clause and map it;
    pmapping = findUnitClause(clauses, model);
    if (pmapping != null){
      Variable p = (Variable) pmapping.elementAt(0);
      Boolean pvalue = (Boolean) pmapping.elementAt(1);
      model.put(p, pvalue);
      symbols.remove(p);
      System.out.println("Unit clause literal " + p.toString() + " assigned " + pvalue.toString());
      return DPLL(clauses, symbols, model); 
    }
    // if none of those, pick a symbol and branch; try mapping true and false,
    // return better of them.
    Interpretation falsemodel = (Interpretation) model.clone();
    Interpretation truemodel = (Interpretation) model.clone();
    Variable p = (Variable) symbols.toArray()[0];
    System.out.println("No pure or unit, trying " + p.toString()); 
    Object result; // we really don't care about the hashmap return value
    result = falsemodel.put(p, Boolean.FALSE);
    result = truemodel.put(p, Boolean.TRUE);
    symbols.remove(p);
    // keep symbols from getting munged in one iteration and bugging other
    Set falsesymbols = new HashSet(symbols);
    Set truesymbols = new HashSet(symbols);
    Interpretation falseresult = DPLL(clauses, falsesymbols, falsemodel);
    Interpretation trueresult = DPLL(clauses, truesymbols, truemodel);
    if (trueresult != null)
      return trueresult; // it doesn't matter which mapping
    else {
      if (falseresult != null)
	return falseresult;
      else
	return null;
    }
    
  }

  private static Vector findUnitClause(List clauses, Interpretation model){
    // returns a vector which is null if no unit clause exists,
    // and which contains the variable at 0 and its value at 1 if one does
    Vector assignment = new Vector();
    Iterator clauseiterator = clauses.iterator();
    // iterate over clauses
    while (clauseiterator.hasNext()){
      Disjunction thisclause = (Disjunction) clauseiterator.next();
      // for each clause, test if unit
      Sentence literal = isUnitClause(thisclause, model);
      // if so, find variable-value pair to make clause true
      if (literal != null){
	Set pset = literal.getVariables();
	Iterator setit = pset.iterator();
	Variable p = (Variable) setit.next();
	Boolean pval = null;
	if (literal.getClass().getName().lastIndexOf("Negation") != -1)
	  pval = Boolean.FALSE;
	if (literal.getClass().getName().lastIndexOf("Variable") != -1)
	  pval = Boolean.TRUE;
	assignment.add(p);
	assignment.add(pval);
	System.out.println("Unit clause mapping" + literal.toString() + " to " + pval.toString());
	return assignment;
	// return said pair
      }
    }
    // if no such clause, return null
    return null;
  }

  private static Sentence isUnitClause(Disjunction clause, Interpretation model){
    // returns null if is not a unit clause; else returns literal
    // of unit
    Vector unassigned = new Vector();
    if (clause.isSatisfied(model) !=null) // clause has a truth value already
      return null;
    else{
    List literals = clause.getClauses();
    Iterator litit = literals.iterator();
    while ((litit.hasNext()) && (unassigned.size()<3)){
      Sentence thisliteral = (Sentence) litit.next();
      if (thisliteral.isSatisfied(model) == null)
	unassigned.add(thisliteral);
    }
    if (unassigned.size() == 1) // only one unknown, others false
      { Sentence unitliteral = (Sentence) unassigned.elementAt(0);
      return unitliteral;}
    else return null;
    }
  }
  
  private static Vector getPureSymbol(Set symbols, List clauses, Interpretation model){
    // returns a vector which is null if no pure symbols exist,
    // and which contains the variable at 0 and its value at 1 if one does.

    // Iterate over symbols
    Vector puresymbol = new Vector();
    Iterator symbolit = symbols.iterator();
    while (symbolit.hasNext()){
      Variable thissymbol = (Variable) symbolit.next();
      if (!(model.containsKey(thissymbol))){ // we don't already have a mapping
	
    // for each symbol, determine if it's pure
	Boolean pureresult = isPureSymbol(thissymbol, clauses, model);
	if (pureresult != null){
    // if so, assign value to make the literal true and return
	  puresymbol.add(thissymbol);
	  puresymbol.add(pureresult); 
	  return puresymbol;
	}
      }
    }
    // if end without finding, return null
    return null;
  }
  

  // isPureSymbol returns null if symbol is not pure, true if symbol is purely
  // positive, and false if symbol is purely negative, so that non-null output
  // is equivalent to the value to make all instances true.
  
  private static Boolean isPureSymbol(Variable symbol, List clauses, Interpretation model){

    boolean isPositive = false;
    boolean isNegative = false;

    Iterator clauseit = clauses.iterator(); 
    while (clauseit.hasNext()){
    // for each clause:
      Disjunction thisclause = (Disjunction) clauseit.next();
    // if clause is _not already true_ (we can ignore those)
      if (!(thisclause.isSatisfied(model) == Boolean.TRUE)){
	List literals = thisclause.getClauses();
	Iterator litit = literals.iterator();
	while (litit.hasNext()){
    // check each literal to see if it contains symbol
	  Sentence thislit = (Sentence) litit.next();
	  if (thislit.getVariables().contains(symbol)){
    // if so, determine if it is positive or negative
	    if (thislit.getClass().getName().lastIndexOf("Negation") != -1)
	      isNegative = true;
	    if (thislit.getClass().getName().lastIndexOf("Variable") != -1)
	      isPositive= true;
    // set booleans accordingly
	  }
	}
      }
    }
      
    // when done, if only one of isPositive and isNegative is true,
    // symbol is pure; which tells us which kind of pure.
    if (isPositive || isNegative){
      if (isPositive && isNegative)
	return null;
      else{
	if (isPositive)
	  return Boolean.TRUE;
	if (isNegative)
	  return Boolean.FALSE;
      }}
      return null;
  }

  public String solve(Sentence input){
    String output;
    if (input instanceof Conjunction){
      Conjunction problem = (Conjunction) input;
      System.out.println("Testing conjunction " + problem.toString());
      Interpretation soln = satisfiable(problem);
      if (soln != null)
	output = soln.toString();
      else
	output = "No Solution";
    }
  else
    output = "No Solution";
  return output;
  }

  
  public static void main(String args[]){
    // args should contain the name of the file we're parsing
   
//      String filename = args[0];
      File inputfile = new File("C:\\Users\\user\\Desktop\\kusum\\workspace\\eclipse\\SATSolver\\satisfiable2.cnf");
      Conjunction problem = CNF.parse(inputfile);
      System.out.println("Testing conjunction " + problem.toString());
      Interpretation soln = satisfiable(problem);
      if (soln != null)
	System.out.println(soln.toString());
      else
	System.out.println("No Solution");
    
  }
  

  
}
