package walksat;

/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.util.Iterator;
import java.util.Vector;

/**
 *
 * @author user
 */
public class SAT {
    
    int NO_VALUE = -1;
    
    int _numberOfVariables = 0 , _numberOfClauses = 0;
    int domain[] = {1,0};
    int assignments[] ;
    CSP csp;
    
    public SAT(String filename)
    {
        System.out.println("Min Conflicts");
        csp = generateConstraints(filename);
        assignments = new int[_numberOfVariables];
        for (int i = 0; i < _numberOfVariables; i++) {
            assignments[i] = 1; // initial assignment
        }
        long max_steps = (long)(_numberOfVariables*_numberOfClauses);
        boolean result = min_conflicts(max_steps);
        if(result){
            System.out.println("s Satisfiable");
            int value = 0;
            System.out.print("v");
            for(int index = 0 ; index < _numberOfVariables ; index++ )
            {
                value = index+1;
                value *= (assignments[index]==1)? 1 : -1;
                System.out.print(" "+value);
            }
            System.out.print(" 0");
            System.out.println();
        }
        else {
            System.out.println("Unsatisfiable");
        }
    }
    
    public boolean min_conflicts(long max_steps)
    {
        // current is assignments
        int conflicts[] = new int[_numberOfVariables];
        
        for(long index=0 ; index<max_steps;index++)
        {
            initializeConflicts(conflicts);
            boolean result = CheckResult(assignments, conflicts);
            if(result==true)
                return true;
            int key = maxconflicts(conflicts);
            int val = assignments[key] ;
            val = (val+1)%2;
            assignments[key] = val;
        }
        return false;
    }
    
    public int maxconflicts(int conflicts[])
    {
        int count = conflicts[0] ;
        Vector v = new Vector();
        for (int i = 0; i < conflicts.length; i++) {
            if(conflicts[i]!=0) {
                v.add(i);
            }
        }
        int index = (int)(Math.random()*v.size());
        return (Integer)v.get(index);
    }
    
    public void initializeConflicts(int conflicts[])
    {
        for (int i = 0; i < conflicts.length; i++) {
            conflicts[i]=0;
        }
    }
    
    public boolean CheckResult(int assignment[],int conflicts[])
    {
        int global_status = 1;
        for (Clause constraint : csp.constraints) {
            global_status&=checkClauseResult(constraint, assignment,conflicts);
        }
     return (global_status==1)?true:false;   
    }
    
    /**
     *
     * @param constraint
     * @param assignment
     * @param conflicts
     * @return
     */
    public int checkClauseResult(Clause constraint , int assignment[],int conflicts[])
    {
        int val = 0;
        Vector possibleConflicts = new Vector(constraint.variable.length);        
        for(Variable cspvar:constraint.variable)
        {
            int key = abs(cspvar.key);
            int value = assignment[key-1];
            value = (cspvar.key<0)?(value+1)%2:value;
            val|=value;
            possibleConflicts.add(key);
        }
        if(val==0)
        {
            for (Iterator it = possibleConflicts.iterator(); it.hasNext();) {
                int key = (Integer)it.next();
                conflicts[key-1]+=1;     
            }
        }
        return val;
        
    }
    
    public int abs(int value)
    {
        return (value>=0)?value:-value;
    }
    
    public CSP generateConstraints(String filename)
    {
        Vector<String> clauses = parseFile(filename);
        return generateClauses(clauses);
    }
    
    public CSP generateClauses(Vector<String> clauses)
    {
        CSP csp = new CSP();
        csp.constraints = new Clause[clauses.size()];
        int clause_index = 0;
        for (Iterator<String> it = clauses.iterator(); it.hasNext();) {
            String string = it.next();
            String split[] = string.split(" ");
            Clause clause = new Clause();
            clause.variable = new Variable[split.length-1]; // last 0 is not counted
            int variable_index = 0 ;
            for (String string1 : split) {
                int value = Integer.parseInt(string1);
                if(value==0) break;
                Variable var = new Variable();
                var.key = value;
                clause.variable[variable_index] = var;
                variable_index++;
            }
           csp.constraints[clause_index] = clause;
           clause_index++;
        }
        return csp;
    }
    
    public Vector<String> parseFile(String filename)
    {
        try
        {
            FileInputStream filestream = new FileInputStream(filename);
            DataInputStream in = new DataInputStream(filestream);
            BufferedReader br = new BufferedReader(new InputStreamReader(in));
            String line;
            int lineNumber=0,clauseIndex=0;
            Vector<String> clauses = new Vector<String>();
            while((line=br.readLine())!=null)
            {
                lineNumber++;
                switch(lineNumber)
                {
                    case 1:
                        //Nothing much to do .Its just a comment line in .cnf file
                    break;
                    case 2:
                        String temp[] = line.split(" ");
                        _numberOfVariables = Integer.parseInt(temp[2]);
                        _numberOfClauses = Integer.parseInt(temp[3]);
                        break;
                    default:
                        clauses.add(line);
                        clauseIndex++;
                    break;
                }
            }
            return clauses;
            
        }catch(Exception e)
        {
            System.out.println(e.getMessage());
            return null;
        }
    }
    
    public static void main(String args[])
    {
//        SAT satMinConflicts = new SATMin("case\\generated\\gen-1\\gen-1.2\\unif-c2100-v600-s1765710634.cnf");
    }
    
}


class Variable
{
    int key;
    int currentValue=-1;
}

class CSP
{
    Clause constraints[];
    boolean global_status = false;
}

class Clause
{
    Variable variable[];
    boolean local_status = false;
}