import { reduxForm } from 'redux-form'
import TakeArbitraryLine from '../../components/Proof/TakeArbitraryLine'
import { closeProofStep, takeArbitrary } from '../../actions'

const mapDispatchToProps = (dispatch) => (
  {
    onCloseClick: () => dispatch(closeProofStep())
  }
)

const submit = (values, dispatch) => {
  return new Promise((resolve, reject) => {
    if (!values.name) {
      reject({ name: "Undefined" })
    } else if (!values.domain) {
      reject ({ domain: "Undefined" })
    } else {
      dispatch(takeArbitrary(values.name, values.domain))
        .then(() => resolve())
        .catch(() => reject({ name: "Name clash" }))
    }
  })
}

export default reduxForm({
  form: "addArbitraryLine",
  fields: ["name", "domain"],
  onSubmit: submit
}, null, mapDispatchToProps)(TakeArbitraryLine)

