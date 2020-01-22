import io.kotlintest.shouldBe
import io.kotlintest.shouldThrow
import io.kotlintest.specs.StringSpec
import org.abs_models.crowbar.main.*
import org.abs_models.crowbar.types.PostInvType
import java.nio.file.Paths

class PostInvTest : StringSpec ({
	val postInv = PostInvType::class
	"typeerror"{
		shouldThrow<Exception> {
			load(listOf(Paths.get("src/test/resources/exception.abs")))
		}
	}
	for( smt in listOf("z3","cvc")) {
		println("testing with: $smt as backend")
		smtPath = smt
		"$smt success"{
			val (model, repos) = load(listOf(Paths.get("src/test/resources/success.abs")))
			val classDecl = model.extractClassDecl("Success", "C", repos)
			classDecl.executeAll(repos,postInv) shouldBe true
		}
		"$smt types"{
			val (model, repos) = load(listOf(Paths.get("src/test/resources/types.abs")))
			val classDecl = model.extractClassDecl("Types", "C", repos)

			val iNode = classDecl.extractInitialNode(postInv)
			executeNode(iNode, repos, postInv) shouldBe true

			val sNode = classDecl.extractMethodNode(postInv,"m", repos)
			executeNode(sNode, repos, postInv) shouldBe true

			val fNode = classDecl.extractMethodNode(postInv,"m2", repos)
			executeNode(fNode, repos, postInv) shouldBe false

		}
		"$smt ints"{
			val (model, repos) = load(listOf(Paths.get("src/test/resources/ints.abs")))
			val classDecl = model.extractClassDecl("Ints", "C", repos)
			classDecl.executeAll(repos, postInv) shouldBe true

			val mNode = model.exctractMainNode(postInv)
			executeNode(mNode, repos, postInv) shouldBe true
		}
		"$smt guards"{
			val (model, repos) = load(listOf(Paths.get("src/test/resources/guards.abs")))
			val classDecl = model.extractClassDecl("Guard", "C", repos)

			val m1Node = classDecl.extractMethodNode(postInv,"msucc", repos)
			executeNode(m1Node, repos, postInv) shouldBe true

			val m2Node = classDecl.extractMethodNode(postInv,"mfail", repos)
			executeNode(m2Node, repos, postInv) shouldBe false
		}
		"$smt fails"{
			val (model, repos) = load(listOf(Paths.get("src/test/resources/fail.abs")))
			val classDecl = model.extractClassDecl("Fail", "C", repos)

			val iNode = classDecl.extractInitialNode(postInv)
			executeNode(iNode, repos, postInv) shouldBe false

			for (m in classDecl.methods) {
				val node = classDecl.extractMethodNode(postInv,m.methodSig.name, repos)
				executeNode(node, repos, postInv) shouldBe false
			}
			val classDecl2 = model.extractClassDecl("Fail", "D", repos)
			val node2 = classDecl2.extractMethodNode(postInv,"failure", repos)
			executeNode(node2, repos, postInv) shouldBe false
		}
		"$smt create"{
			val (model, repos) = load(listOf(Paths.get("src/test/resources/create.abs")))
			val classDecl = model.extractClassDecl("Create", "C", repos)

			val iNode = classDecl.extractInitialNode(postInv)
			executeNode(iNode, repos, postInv) shouldBe true

			val sNode = classDecl.extractMethodNode(postInv,"success", repos)
			executeNode(sNode, repos, postInv) shouldBe true

			val fNode = classDecl.extractMethodNode(postInv,"fail", repos)
			executeNode(fNode, repos, postInv) shouldBe false

			val mNode = model.exctractMainNode(postInv)
			executeNode(mNode, repos, postInv) shouldBe true
		}
		"$smt reference"{
			val (model, repos) = load(listOf(Paths.get("src/test/resources/reference.abs")))
			val classDecl = model.extractClassDecl("Reference", "C", repos)

			val iNode = classDecl.extractInitialNode(postInv)
			executeNode(iNode, repos, postInv) shouldBe true

			val m1Node = classDecl.extractMethodNode(postInv,"m1", repos)
			executeNode(m1Node, repos, postInv) shouldBe false

			val m2Node = classDecl.extractMethodNode(postInv,"m2", repos)
			executeNode(m2Node, repos, postInv) shouldBe false //see comment in file

			val m3Node = classDecl.extractMethodNode(postInv,"m3", repos)
			executeNode(m3Node, repos, postInv) shouldBe true

			val m4Node = classDecl.extractMethodNode(postInv,"m4", repos)
			executeNode(m4Node, repos, postInv) shouldBe true

			val mNode = model.exctractMainNode(postInv)
			executeNode(mNode, repos, postInv) shouldBe false
		}
		"$smt multi"{
			val (model, repos) = load(listOf(Paths.get("src/test/resources/multi1.abs"), Paths.get("src/test/resources/multi2.abs")))
			val classDecl = model.extractClassDecl("Multi1", "C", repos)
			classDecl.executeAll(repos, postInv) shouldBe true

			val mNode = model.exctractMainNode(postInv)
			executeNode(mNode, repos, postInv) shouldBe true
		}
		"$smt callsuccess"{
				val (model, repos) = load(listOf(Paths.get("src/test/resources/callsimplesuccess.abs")))
				val classDeclC = model.extractClassDecl("CallS", "C", repos)
				classDeclC.executeAll(repos,postInv) shouldBe true
				val classDeclD = model.extractClassDecl("CallS", "D", repos)
				classDeclD.executeAll(repos,postInv) shouldBe true
				val mNode = model.exctractMainNode(postInv)
				executeNode(mNode, repos, postInv) shouldBe true
		}
		"$smt callfail"{
			val (model, repos) = load(listOf(Paths.get("src/test/resources/callsimplefail.abs")))
			val classDeclC = model.extractClassDecl("CallF", "C", repos)
			val m0Node = classDeclC.extractMethodNode(postInv, "m", repos)
			executeNode(m0Node, repos, postInv) shouldBe false
			val classDeclD = model.extractClassDecl("CallF", "D", repos)
			val m1Node = classDeclD.extractMethodNode(postInv, "m", repos)
			executeNode(m1Node, repos, postInv) shouldBe false
			val classDeclE = model.extractClassDecl("CallF", "E", repos)
			val m2Node = classDeclE.extractMethodNode(postInv, "m", repos)
			executeNode(m2Node, repos, postInv) shouldBe false
			val mNode = model.exctractMainNode(postInv)
			executeNode(mNode, repos, postInv) shouldBe false
		}
		"$smt selfcall"{
			val (model, repos) = load(listOf(Paths.get("src/test/resources/selfcall.abs")))
			val classDecl = model.extractClassDecl("Self", "C", repos)
			val m0Node = classDecl.extractMethodNode(postInv, "n", repos)
			executeNode(m0Node, repos, postInv) shouldBe true
			val m1Node = classDecl.extractMethodNode(postInv, "m", repos)
			executeNode(m1Node, repos, postInv) shouldBe true
			val m2Node = classDecl.extractMethodNode(postInv, "m2", repos)
			executeNode(m2Node, repos, postInv) shouldBe false
			val mNode = model.exctractMainNode(postInv)
			executeNode(mNode, repos, postInv) shouldBe true

		}
	}
})