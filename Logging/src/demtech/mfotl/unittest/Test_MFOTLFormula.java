package demtech.mfotl.unittest;

import static org.junit.Assert.*;

import java.util.Arrays;
import java.util.Collection;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import demtech.mfotl.MFOTLFormula;
import demtech.mfotl.Signature;

@RunWith(value = Parameterized.class)
public class Test_MFOTLFormula {
    private final MFOTLFormula my_mfotl;
    private final Signature my_signature = TestSetting.initializeSignature("./src/demtech/mfotl/e1.sig");
    
    public Test_MFOTLFormula(final String a_fs) {
        my_mfotl = new MFOTLFormula(a_fs, my_signature);
    }
    
    @Parameters
    public static Collection<String[]> data() {
        String[][] data = new String[][] {{"out ( 5 )"}, {"in ( 3 )"}, {"True"}, {"False"}, {"True "}};
        return Arrays.asList(data);
    }

    @Before
    public void setUp() throws Exception {
    }

    @After
    public void tearDown() throws Exception {
    }

    @Test
    public void testLexer() {
        System.out.println(my_mfotl.toString());
    }
}
