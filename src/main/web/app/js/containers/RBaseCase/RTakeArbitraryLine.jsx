import { reduxForm } from 'redux-form'
import TakeArbitraryLine from '../../components/BaseCase/TakeArbitraryLine'
import { closeBaseCaseProofStep, takeArbitrary } from '../../actions'

const mapDispatchToProps = (dispatch) => (
  {
    onCloseClick: () => dispatch(closeBaseCaseProofStep())
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
    //   dispatch(takeArbitrary(values.name, values.domain, "BASE_CASE"))
    //     .then(() => resolve())
    //     .catch(() => reject({ name: "Name clash" }))
    // }
  })
}

export default reduxForm({
  form: "addBaseCaseArbitraryLine",
  fields: ["name", "domain"],
  onSubmit: submit
}, null, mapDispatchToProps)(TakeArbitraryLine)

