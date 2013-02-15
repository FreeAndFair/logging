package mobius.logging.mfotl;

//TODO add specs and docs

import java.io.PrintStream;

public class Logger {
    private final PrintStream logger_inst;
    
    public Logger() {
        logger_inst = getLogger();
    }
    
    private PrintStream getLogger() {
        return System.out;
    }
    
    public void debug(final String _debug) {
        logger_inst.println(_debug);
    }
    
    public void info(final String _info) {
        logger_inst.println(_info);
    }
    
    /*
     * fatal information, exit after output it
     */
    public void fatal(final String _fatal) {
        logger_inst.println(_fatal);
        System.exit(0);
    }
    
    /*
     * fatal information, exit after output it
     */
    public void error(final String _error) {
        logger_inst.println(_error);
        System.exit(1);
    }
}