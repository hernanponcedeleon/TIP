package tip.analysis

import tip.ast._
import tip.cfg.{CfgNode, CfgStmtNode, IntraproceduralProgramCfg}
import tip.lattices.{MapLattice, PowersetLattice}
import tip.solvers.{SimpleMapLatticeFixpointSolver, SimpleWorklistFixpointSolver}
import tip.ast.AstNodeData.DeclarationData

/**
  * Base class for reaching definitions analysis.
  */
abstract class ReachingDefAnalysis(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData) extends FlowSensitiveAnalysis[CfgNode](cfg) {

  import tip.cfg.CfgOps._
  import tip.ast.AstOps._

  val allAssignments: Set[AAssignStmt] = cfg.nodes.map(_.appearingAssignments).foldLeft(Set[AAssignStmt]()) { (a, x) =>
    x.map(a + _).getOrElse(a)
  }

  val lattice = new MapLattice(cfg.nodes, new PowersetLattice(allAssignments))

  NoPointers.assertContainsProgram(cfg.prog)
  NoRecords.assertContainsProgram(cfg.prog)

  def transfer(n: CfgNode, s: lattice.sublattice.Element): lattice.sublattice.Element =
  n match {
      case r: CfgStmtNode =>
        r.data match {
          case ass: AAssignStmt =>
            ass.left match {
              case id: AIdentifier =>
                s.filter { e =>
                  !(id.appearingIds subsetOf ((e: AAssignStmt).left.asInstanceOf[AIdentifier]).appearingIds)
                } + ass
              case _ => s
            }
          case _ => s
        }
      case _ => s
    }
}

/**
  * Reaching definition analysis that uses the simple fixpoint solver.
  */
class ReachingDefAnalysisSimpleSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
    extends ReachingDefAnalysis(cfg)
    with SimpleMapLatticeFixpointSolver[CfgNode]
    with ForwardDependencies

/**
  * Reaching definition analysis that uses the worklist solver.
  */
class ReachingDefAnalysisWorklistSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
    extends ReachingDefAnalysis(cfg)
    with SimpleWorklistFixpointSolver[CfgNode]
    with ForwardDependencies
