package zchaff;

import java.io.BufferedReader;
import java.io.DataInputStream;
import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Vector;

public class sat {
	
	public sat(String filename)
	{
		
	}
	
	public void read_cnf(chaff_solver mng,String filename)
    {
        try
        {
            FileInputStream filestream = new FileInputStream(filename);
            DataInputStream in = new DataInputStream(filestream);
            BufferedReader br = new BufferedReader(new InputStreamReader(in));
            String line;
            int lineNumber=0,clauseIndex=0;
            Vector<Integer> clause_vars = new Vector<Integer>();
            Vector<Integer> clause_lits = new Vector<Integer>();
            while((line=br.readLine())!=null)
            {
            	line=line.trim();
            	if(line.equals("")) continue;
                lineNumber++;
                if(line.startsWith("c"))
                {
                	//Nothing much to do .Its just a comment line in .cnf file
                	continue;
                }
                else if(line.startsWith("p"))
                {
                	String temp[] = line.split(" ");
                    int _numberOfVariables = Integer.parseInt(temp[2]);
//                    int _numberOfClauses = Integer.parseInt(temp[3]);
                    mng.SAT_SetNumVariables(_numberOfVariables);
                }
                else
                {
                	String splitString[] = (line.trim()).split(" ");
                	for (int i = 0; i < splitString.length-1; i++) { // last var is zero
						String string = splitString[i];
						int var_idx = Integer.parseInt(string);
						int sign = (var_idx>0)?0:1;
						var_idx = (var_idx>0)?var_idx:-var_idx;
						clause_vars.add(var_idx);
						clause_lits.add((var_idx>>1)+sign);
					}
                	int groupid = 0; // original clauses
//                	mng.SAT_AddClause(clause_lits, clause_lits.size() ,groupid);
                }
            }
            
        }catch(Exception e)
        {
            System.out.println(e.getMessage());
        }
    }
	
	public static void main(String args[])
	{
		
	}
	
}


class solver
{
	
}


class Literal
{
	int _lits_count =0;
	int _2_lits_count[] = new int[2];
	ArrayList<Integer> cls_idx = new ArrayList<Integer>();
}

class Clause
{
	int watched[] = new int[2]; // variable index
}

class CSP
{
	ArrayList<Clause> clauses;
}
