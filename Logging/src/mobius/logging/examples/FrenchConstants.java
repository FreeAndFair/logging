/*
 * Software Engineering Tools.
 *
 * $Id: FrenchConstants.jass,v 1.1.1.1 2002/12/29 12:36:18 kiniry Exp $
 *
 * Copyright (c) 1997-2001 Joseph Kiniry
 * Copyright (c) 2000-2001 KindSoftware, LLC
 * Copyright (c) 1997-1999 California Institute of Technology
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * - Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 *
 * - Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 *
 * - Neither the name of the Joseph Kiniry, KindSoftware, nor the
 * California Institute of Technology, nor the names of its contributors
 * may be used to endorse or promote products derived from this software
 * without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS ``AS
 * IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL KIND SOFTWARE OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package mobius.logging.examples;

import java.util.Map;
import mobius.logging.DebugConstants;

/**
 * <p> FrenchConstants is an interface that collects the various constants
 * of the debugging package including debug level ranges, standard
 * debugging messages, etc.  It is a sub-type of DebugConstants and is used
 * as an example of how to modify the semantics (customize) the debug
 * package. </p>
 *
 * @version alpha-1
 * @author Joseph R. Kiniry (kiniry@acm.org)
 * @see DebugConstants
 *
 * @note An example extension to the mobius.logging package.
 */
//+@ nullable_by_default
public interface FrenchConstants extends DebugConstants {
  // Public Attributes

  /**
   * The minimum debug level.
   *
   * @design Note that debugging level still must be
   * <EM>incremental</EM> I.e. A debug level of k is <EM>lower
   * than/less important than</EM> a debug level of k+1.
   */
  int LEVEL_MIN = 1;

  /**
   * The maximum debug level.
   */
  int LEVEL_MAX = 100;

  // Various messages that can be localized or otherwise customized.
  /** What is an error called? */
  String ERROR_STRING = "l'error";
  /** What is a failed assertion called? */
  String FAILED_ASSERTION_STRING = "affirmation echouee";

  /**
   * @design The default categories are as follows:
   * <table align="abscenter" border="1" cellspacing="0" cellpadding="0">
   * <tr>
   * <td> <strong>Category</strong> </td>
   * <td> <strong>Level</strong> </td>
   * <td> <strong>Description</strong> </td>
   * </tr>
   * <tr>
   * <td> AFFIRMATION </td>
   * <td> 9 </td>
   * <td> The highest level category that exists.  Assertions are
   * predicates that <strong>must</strong> be true.  If an assertion
   * is false, a stack dump takes place and the object in question
   * should shut down in an orderly fashion.
   * Note that a single assertion should be made for each predicate
   * that is in the precondition, postcondition, requires, and ensures
   * expressions for every method. </td>
   * </tr>
   * <tr>
   * <td> PANNE </td>
   * <td> 9 </td>
   * <td> The highest level category that exists.  Sometimes a object
   * need fail outside an assertion.  This default category provides
   * this functionality.  If a failure is seen, a stack dump takes
   * place and the object in question should shut down in an orderly
   * fashion.</td>
   * </tr>
   * <tr>
   * <td> CRITIQUE </td>
   * <td> 7 </td>
   * <td> Very important problems/errors that will eventually cause
   * Failures or Assertions should be tagged as Critical.  The
   * user/system must be information of such problems but the object
   * in question need not shut down immediately and can potentially
   * recover.  Typical examples of Critical errors are resource-related
   * errors (out of memory, disk space, CPU time, etc.).</td>
   * </tr>
   * <tr>
   * <td> ERREUR </td>
   * <td> 5 </td>
   * <td> This is the standard error level.  An Error means "something
   * went wrong and the user should probably be notified whether the
   * the system can automatically recover properly or not".</td>
   * </tr>
   * <tr>
   * <td> AVERTISSEMENT </td>
   * <td> 3 </td>
   * <td> A warning is a message that says something has gone wrong
   * but it's not terribly serious.  Warnings are often, but not always,
   * communicated on to the user.</td>
   * </tr>
   * <tr>
   * <td> NOTIFICATION </td>
   * <td> 1 </td>
   * <td> A notice is simply a progress message.  Notices are used to
   * track a thread of control during debugging.</td>
   * </tr>
   * </table>
   */

  // The default debugging levels are pre-defined to simplify the use
  // of the print() and println() functions for simple debugging.

  /** The level of an assertion. */
  int ASSERTION_LEVEL = 90;
  /** The level of an failure. */
  int FAILURE_LEVEL = 90;
  /** The level of an critical. */
  int CRITICAL_LEVEL = 70;
  /** The level of an error. */
  int ERROR_LEVEL = 50;
  /** The level of an warning. */
  int WARNING_LEVEL = 30;
  /** The level of an notice. */
  int NOTICE_LEVEL = 10;

  // The default debugging categories are pre-defined to simplify the
  // use of the print() and println() functions for simple debugging.

  /** The French translation of 'assertion'. */
  String ASSERTION = "AFFIRMATION";
  /** The French translation of 'failure'. */
  String FAILURE = "PANNE";
  /** The French translation of 'critical'. */
  String CRITICAL = "CRITIQUE";
  /** The French translation of 'error'. */
  String ERROR = "ERREUR";
  /** The French translation of 'warning'. */
  String WARNING = "AVERTISSEMENT";
  /** The French translation of 'notification'. */
  String NOTICE = "NOTIFICATION";

  // Error conditions for the Debug class.

  /** Indicates that an invalid thread was used. */
  int INVALID_THREAD = -1;

  // Public Methods

  /** {@inheritDoc} */
  void initCategories(/*@ non_null @*/ Map the_categories_map);

} // end of interface FrenchConstants

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */
