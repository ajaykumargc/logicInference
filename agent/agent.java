import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;

class agent
{
    private ArrayList<String> toProvelist = new ArrayList<String>();

    private ArrayList<String> assertions = new ArrayList<String>();

    private ArrayList<String> clauses = new ArrayList<String>();

    private ArrayList<String> processedList = new ArrayList<String>();

    public static HashSet<String> substituteTest(String tp, ArrayList<String> rules)
    {
        // String tpc = tp;

        HashSet<String> test = new HashSet();
        String ret = "";
        for (int i = 0; i < rules.size(); i++)
        {
            if (rules.get(i).contains("=>"))
            {
                continue;
            }
            else
            {
                if (rules.get(i).contains(","))
                {
                    ret = rules.get(i).split("\\(")[1].split(",")[0];
                    test.add(ret);
                }
                else
                {
                    String temp = rules.get(i).split("\\(")[1];
                    ret = temp.replace(")", "");
                    test.add(ret);
                }
            }
        }
        return test;
    }

    public boolean backwardChainAlgo()
    {
        while (!toProvelist.isEmpty())
        {
            String toprove = toProvelist.remove(toProvelist.size() - 1);
            processedList.add(toprove);

            if (!assertions.contains(toprove))
            {
                ArrayList<String> tempAsserts = new ArrayList<String>();
                for (int i = 0; i < clauses.size(); i++)
                {
                    if (isMatch(clauses.get(i), toprove))
                    {
                        ArrayList<String> temp = getLHS(clauses.get(i));
                        for (int j = 0; j < temp.size(); j++)
                        {
                            tempAsserts.add(temp.get(j));
                        }
                    }
                }

                if (tempAsserts.size() == 0)
                {
                    return false;
                }
                else
                {
                    for (int i = 0; i < tempAsserts.size(); i++)
                    {
                        if (!processedList.contains(tempAsserts.get(i)))
                        {
                            toProvelist.add(tempAsserts.get(i));
                        }
                    }

                }
            }

        }
        return true;
    }

    public boolean isMatch(String clause, String toCheck)
    {
        String temp = clause.split("=>")[1];
        if (temp.equals(toCheck))
        {
            return true;
        }
        else
        {
            return false;
        }
    }

    public ArrayList<String> getLHS(String clause)
    {
        String lhs = clause.split("=>")[0];
        ArrayList<String> temp = new ArrayList<String>();
        String[] templhs = lhs.split("&");

        for (int i = 0; i < templhs.length; i++)
        {
            if (!toProvelist.contains(templhs[i]))
            {
                temp.add(templhs[i]);
            }
        }
        return temp;
    }

    public static String substitute(String tp, ArrayList<String> rules)
    {
        for (int i = 0; i < rules.size(); i++)
        {
            String tpc = tp;
            String[] re = tpc.split("\\(");
            String temp = rules.get(i);
            String tempL[];
            if (temp.contains("=>"))
            {
                tempL = temp.split("=>");

                if (tempL[1].contains(re[0]))
                {
                    if (re[1].contains(","))
                    {
                        String[] tmp = re[1].split(",");
                        String[] tmpR = tempL[1].split("\\(")[1].split(",");

                        if (tmpR[0].startsWith("x"))
                        {
                            // retrun tmp[0] as x substitute value
                            return tmp[0];
                        }
                        else
                        {
                            // return tmp[1] as x substitute value
                            tmp[1].replace(")", "");
                            return tmp[1];
                        }
                    }
                    else
                    {
                        String[] tmpR = tempL[1].split("\\(");
                        if (tmpR[1].startsWith("x"))
                        {
                            re[1].replace(")", "");
                            return re[1];
                        }
                        else
                        {
                            continue;
                        }
                    }
                }
                else
                {
                    continue;
                }
            }
            else
            {
                // its fact
                if (temp.contains(re[0]))
                {
                    if (re[1].contains(","))
                    {
                        String[] tmp = re[1].split(",");
                        String[] tmpR = temp.split("\\(")[1].split(",");

                        if (tmpR[0].startsWith("x"))
                        {
                            // retrun tmp[0] as x substitute value
                            return tmp[0];
                        }
                        else
                        {
                            // return tmp[1] as x substitute value
                            tmp[1].replace(")", "");
                            return tmp[1];
                        }
                    }
                    else
                    {
                        String[] tmpR = temp.split("\\(");
                        if (tmpR[1].startsWith("x"))
                        {
                            re[1].replace(")", "");
                            return re[1];
                        }
                        else
                        {
                            continue;
                        }
                    }
                }
                else
                {
                    continue;
                }
            }
        }
        return "";
    }

    public static void main(String[] args)
    {
        File fin = new File("input.txt");
        String toProve = "";
        @SuppressWarnings("unused")
        String rulesNum = "";
        ArrayList<String> Rules = new ArrayList<String>();
        try
        {
            FileInputStream fis = new FileInputStream(fin);
            BufferedReader br = new BufferedReader(new InputStreamReader(fis));
            String line = null;

            toProve = br.readLine();
            rulesNum = br.readLine();

            while ((line = br.readLine()) != null)
            {
                Rules.add(line);
            }

            br.close();
        }
        catch (IOException e)
        {
            // log exception
        }

        HashSet<String> sub = substituteTest(toProve, Rules);
        Iterator<String> iter = sub.iterator();
        String retValue = "FALSE";

        while (iter.hasNext())
        {
            agent tempObj = new agent();
            String subi = iter.next();
            String tr = "(" + subi;
            ArrayList<String> unified = new ArrayList<String>();
            for (int i = 0; i < Rules.size(); i++)
            {
                String temp = Rules.get(i);
                String tem = temp.replace("(x", tr);
                unified.add(tem);
            }

            // System.out.println(subi);

            tempObj.toProvelist.add(toProve);
            for (int i = 0; i < unified.size(); i++)
            {
                if (unified.get(i).contains("=>"))
                {
                    tempObj.clauses.add(unified.get(i));
                }
                else
                {
                    tempObj.assertions.add(unified.get(i));
                }
            }

            if (tempObj.backwardChainAlgo())
            {
                retValue = "TRUE";
                break;
            }
            else
            {
                retValue = "FALSE";
            }
        }
        // System.out.println(retValue);

        File outfile = new File("output.txt");
        try
        {
            if (!outfile.exists())
            {
                outfile.createNewFile();
            }

            FileWriter fw = new FileWriter(outfile.getAbsoluteFile());
            BufferedWriter bw = new BufferedWriter(fw);
            bw.write(retValue);
            bw.close();
        }
        catch (IOException e)
        {

        }
    }
}
