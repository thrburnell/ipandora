import { reduxForm } from 'redux-form'
import TakeArbitraryLine from '../../components/InductiveCase/TakeArbitraryLine'
import { closeInductiveCaseProofStep, takeArbitrary } from '../../actions'

const mapDispatchToProps = (dispatch) => (
  {
    onCloseClick: () => dispatch(closeInductiveCaseProofStep())
  }
)

const submit = (values, dispatch) => {
  return new Promise((resolve, reject) => {
    console.log("Not yet implemented")
    reject()

    // if (!values.name) {
    //   reject({ name: "Undefined" })
    // } else if (!values.domain) {
    //   reject ({ domain: "Undefined" })
    // } else {
    //   dispatch(takeArbitrary(values.name, values.domain, "INDUCTIVE_CASE"))
    //     .then(() => resolve())
    //     .catch(() => reject({ name: "Name clash" }))
    // }
  })
}

export default reduxForm({
  form: "addInductiveCaseArbitraryLine",
  fields: ["name", "domain"],
  onSubmit: submit
}, null, mapDispatchToProps)(TakeArbitraryLine)

