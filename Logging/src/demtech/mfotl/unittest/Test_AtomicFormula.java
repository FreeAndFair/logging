package demtech.mfotl.unittest;

import static org.junit.Assert.*;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import demtech.mfotl.AtomicFormula;
import demtech.mfotl.Signature;

@RunWith(value = Parameterized.class)
public class Test_AtomicFormula {
    private final AtomicFormula a_atomicformula;
    private final Signature my_signature = TestSetting.initializeSignature("./src/demtech/mfotl/e1.sig");
    
    public Test_AtomicFormula(final String a_afs) {
        a_atomicformula = new AtomicFormula(a_afs.split(" "), my_signature);
    }
    
    @Parameters
    public static Collection<String[]> data() {
        final String[][] data = new String[][] {{"out ( 5 )"}, {"in ( 3 )"}, {"True"}, {"False"}, {"True "}};
        return Arrays.asList(data);
    }
    
    @Test
    public void test() {
        System.out.println(a_atomicformula.toString());
        //fail("Not yet implemented");
    }
}
