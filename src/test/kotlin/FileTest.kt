import io.kotlintest.data.forall
import io.kotlintest.shouldBe
import io.kotlintest.shouldThrow
import io.kotlintest.specs.StringSpec
import io.kotlintest.tables.Row1
import org.abs_models.crowbar.main.*
import java.nio.file.Paths

class FileTest : StringSpec ({
	"success"{
		forall(Row1("z3"),
			Row1("cvc")) {
			println("testing with: $it as backend")
			smtPath = it
			val (model, repos) = load(listOf(Paths.get("src/test/resources/success.abs")))
			val classDecl = model.extractClassDecl("Success", "C", repos)
			classDecl.executeAll(repos) shouldBe true
		}
	}
	"types"{
		forall(Row1("z3"),
			Row1("cvc")) {
			println("testing with: $it as backend")
			smtPath = it
			val (model, repos) = load(listOf(Paths.get("src/test/resources/types.abs")))
			val classDecl = model.extractClassDecl("Types", "C", repos)

			val iNode = classDecl.extractInitialNode()
			executeNode(iNode, repos) shouldBe true

			val sNode = classDecl.extractMethodNode("m", repos)
			executeNode(sNode, repos) shouldBe true

			val fNode = classDecl.extractMethodNode("m2", repos)
			executeNode(fNode, repos) shouldBe false
		}
	}
	"ints"{
		forall(Row1("z3"),
			Row1("cvc")) {
			println("testing with: $it as backend")
			smtPath = it
			val (model, repos) = load(listOf(Paths.get("src/test/resources/ints.abs")))
			val classDecl = model.extractClassDecl("Ints", "C", repos)
			classDecl.executeAll(repos) shouldBe true

			val mNode = model.exctractMainNode()
			executeNode(mNode, repos) shouldBe true
		}
	}
	"fails"{
		forall(Row1("z3"),
			   Row1("cvc")) {
			println("testing with: $it as backend")
			smtPath = it
			val (model, repos) = load(listOf(Paths.get("src/test/resources/fail.abs")))
			val classDecl = model.extractClassDecl("Fail", "C", repos)

			val iNode = classDecl.extractInitialNode()
			executeNode(iNode, repos) shouldBe false

			for (m in classDecl.methods) {
				val node = classDecl.extractMethodNode(m.methodSig.name, repos)
				executeNode(node, repos) shouldBe false
			}
		}
	}
	"create"{
		forall(Row1("z3"),
			Row1("cvc")) {
			println("testing with: $it as backend")
			smtPath = it
			val (model, repos) = load(listOf(Paths.get("src/test/resources/create.abs")))
			val classDecl = model.extractClassDecl("Create", "C", repos)

			val iNode = classDecl.extractInitialNode()
			executeNode(iNode, repos) shouldBe true

			val sNode = classDecl.extractMethodNode("success", repos)
			executeNode(sNode, repos) shouldBe true

			val fNode = classDecl.extractMethodNode("fail", repos)
			executeNode(fNode, repos) shouldBe false

			val mNode = model.exctractMainNode()
			executeNode(mNode, repos) shouldBe true
		}
	}
	"reference"{
	//	forall(Row1("z3"),
			//Row1("cvc")) {
			//println("testing with: $it as backend")
			//smtPath = it
			val (model, repos) = load(listOf(Paths.get("src/test/resources/reference.abs")))
			val classDecl = model.extractClassDecl("Reference", "C", repos)

			val iNode = classDecl.extractInitialNode()
			executeNode(iNode, repos) shouldBe true

			val m1Node = classDecl.extractMethodNode("m1", repos)
			executeNode(m1Node, repos) shouldBe false

			val m2Node = classDecl.extractMethodNode("m2", repos)
			executeNode(m2Node, repos) shouldBe false //see comment in file

			val m3Node = classDecl.extractMethodNode("m3", repos)
			executeNode(m3Node, repos) shouldBe true

			val m4Node = classDecl.extractMethodNode("m4", repos)
			executeNode(m4Node, repos) shouldBe true

			val mNode = model.exctractMainNode()
			executeNode(mNode, repos) shouldBe false
		//}
	}
	"multi"{
		forall(Row1("z3"),
			Row1("cvc")) {
			println("testing with: $it as backend")
			smtPath = it
			val (model, repos) = load(listOf(Paths.get("src/test/resources/multi1.abs"), Paths.get("src/test/resources/multi2.abs")))
			val classDecl = model.extractClassDecl("Multi1", "C", repos)
			classDecl.executeAll(repos) shouldBe true

			val mNode = model.exctractMainNode()
			executeNode(mNode, repos) shouldBe true
		}
	}
	"typeerror"{
		shouldThrow<Exception> {
			load(listOf(Paths.get("src/test/resources/exception.abs")))
		}
	}
	"callsuccess"{
		forall(Row1("z3"),
			Row1("cvc")) {
			println("testing with: $it as backend")
			smtPath = it
			val (model, repos) = load(listOf(Paths.get("src/test/resources/callsimplesuccess.abs")))
			val classDeclC = model.extractClassDecl("CallS", "C", repos)
			classDeclC.executeAll(repos) shouldBe true
			val classDeclD = model.extractClassDecl("CallS", "D", repos)
			classDeclD.executeAll(repos) shouldBe true
			val mNode = model.exctractMainNode()
			executeNode(mNode, repos) shouldBe true
		}
	}
	"callfail"{
		forall(Row1("z3"),
			Row1("cvc")) {
			println("testing with: $it as backend")
			smtPath = it
			val (model, repos) = load(listOf(Paths.get("src/test/resources/callsimplefail.abs")))
			val classDeclC = model.extractClassDecl("CallF", "C", repos)
			val m0Node = classDeclC.extractMethodNode("m", repos)
			executeNode(m0Node, repos) shouldBe false
			val classDeclD = model.extractClassDecl("CallF", "D", repos)
			val m1Node = classDeclD.extractMethodNode("m", repos)
			executeNode(m1Node, repos) shouldBe false
			val classDeclE = model.extractClassDecl("CallF", "E", repos)
			val m2Node = classDeclE.extractMethodNode("m", repos)
			executeNode(m2Node, repos) shouldBe false
			val mNode = model.exctractMainNode()
			executeNode(mNode, repos) shouldBe false
		}
	}
})